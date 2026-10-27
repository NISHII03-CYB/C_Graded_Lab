/*
 * Name: Dehiwattage_Kavindu
 * Surname: Fernando
 * Student ID: 251ADB025
 *
 * Compile:
 * gcc -O2 -Wall -Wextra -std=c17 -o calc calc.c -lm
 *
 * Resources used:
 * https://www.w3schools.com/c/?utm_source=chatgpt.com
 * ChatGPT (OpenAI) - programming guidance and debugging assistance.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#include <errno.h>
#include <dirent.h>
#include <sys/stat.h>

#define FIRST_NAME "yourname"
#define LAST_NAME "yoursurname"
#define STUDENT_ID "yourid"

typedef struct {
    long long integer;
    double floating;
    int is_float;
    size_t start;
} Number;

typedef struct {
    const char *text;
    size_t length;
    size_t position;
    size_t file_offset;
    size_t error_position;
    int failed;
    size_t line_end_position;
} Parser;

typedef struct {
    char *data;
    size_t length;
    size_t capacity;
} StringBuffer;

/* ---------- String buffer ---------- */

static int buffer_append(StringBuffer *b, const char *text, size_t length)
{
    if (b->length + length + 1 > b->capacity) {
        size_t new_capacity = b->capacity == 0 ? 256 : b->capacity;

        while (new_capacity < b->length + length + 1) {
            new_capacity *= 2;
        }

        char *new_data = realloc(b->data, new_capacity);

        if (new_data == NULL) {
            return 0;
        }

        b->data = new_data;
        b->capacity = new_capacity;
    }

    memcpy(b->data + b->length, text, length);
    b->length += length;
    b->data[b->length] = '\0';

    return 1;
}

static int buffer_append_line(StringBuffer *b, const char *text)
{
    return buffer_append(b, text, strlen(text));
}

/* ---------- Parser helpers ---------- */

static void set_error(Parser *p, size_t position)
{
    if (!p->failed) {
        p->failed = 1;
        p->error_position = position;
    }
}

static void set_error_here(Parser *p)
{
    set_error(p, p->file_offset + p->position + 1);
}

static void set_error_at_end(Parser *p)
{
    set_error(p, p->line_end_position);
}

static void skip_spaces(Parser *p)
{
    while (p->position < p->length &&
           (p->text[p->position] == ' ' ||
            p->text[p->position] == '\t' ||
            p->text[p->position] == '\r')) {
        p->position++;
    }
}

static Number make_integer(long long value, size_t start)
{
    Number n;

    n.integer = value;
    n.floating = (double)value;
    n.is_float = 0;
    n.start = start;

    return n;
}

static Number make_float(double value, size_t start)
{
    Number n;

    n.integer = 0;
    n.floating = value;
    n.is_float = 1;
    n.start = start;

    return n;
}

static double number_value(Number n)
{
    if (n.is_float) {
        return n.floating;
    }

    return (double)n.integer;
}

static Number parse_expression(Parser *p);
static Number parse_term(Parser *p);
static Number parse_power(Parser *p);
static Number parse_primary(Parser *p);

/* ---------- Primary: numbers and parentheses ---------- */

static Number parse_primary(Parser *p)
{
    skip_spaces(p);

    size_t start = p->position;

    if (p->position >= p->length) {
        set_error_at_end(p);
        return make_integer(0, start);
    }

    char c = p->text[p->position];

    if (c == '(') {
        p->position++;

        Number result = parse_expression(p);

        skip_spaces(p);

        if (!p->failed) {
            if (p->position >= p->length) {
                set_error_at_end(p);
            } else if (p->text[p->position] != ')') {
                set_error_here(p);
            } else {
                p->position++;
            }
        }

        result.start = start;
        return result;
    }

    if (!isdigit((unsigned char)c)) {
        set_error_here(p);
        return make_integer(0, start);
    }

    while (p->position < p->length &&
           isdigit((unsigned char)p->text[p->position])) {
        p->position++;
    }

    int is_float = 0;

    if (p->position < p->length &&
        p->text[p->position] == '.') {

        size_t dot_position = p->position;

        p->position++;

        if (p->position >= p->length ||
            !isdigit((unsigned char)p->text[p->position])) {
            set_error(p, p->file_offset + dot_position + 1);
            return make_integer(0, start);
        }

        is_float = 1;

        while (p->position < p->length &&
               isdigit((unsigned char)p->text[p->position])) {
            p->position++;
        }
    }

    size_t token_length = p->position - start;

    char *token = malloc(token_length + 1);

    if (token == NULL) {
        set_error_here(p);
        return make_integer(0, start);
    }

    memcpy(token, p->text + start, token_length);
    token[token_length] = '\0';

    errno = 0;
    char *end_pointer;

    if (is_float) {
        double value = strtod(token, &end_pointer);

        free(token);

        if (errno == ERANGE || !isfinite(value)) {
            set_error(p, p->file_offset + start + 1);
            return make_float(0.0, start);
        }

        return make_float(value, start);
    }

    long long value = strtoll(token, &end_pointer, 10);

    free(token);

    if (errno == ERANGE) {
        set_error(p, p->file_offset + start + 1);
        return make_integer(0, start);
    }

    return make_integer(value, start);
}

/* ---------- Exponentiation: right associative ---------- */

static Number parse_power(Parser *p)
{
    Number left = parse_primary(p);

    skip_spaces(p);

    if (p->position + 1 < p->length &&
        p->text[p->position] == '*' &&
        p->text[p->position + 1] == '*') {

        size_t operator_position = p->position;
        p->position += 2;

        skip_spaces(p);

        if (p->position >= p->length) {
            set_error_at_end(p);
            return left;
        }

        if (p->text[p->position] == ')' ||
            p->text[p->position] == '+' ||
            p->text[p->position] == '-' ||
            p->text[p->position] == '*' ||
            p->text[p->position] == '/') {
            set_error_here(p);
            return left;
        }

        size_t exponent_start = p->position;

        Number right = parse_power(p);

        if (p->failed) {
            return left;
        }

        if (!left.is_float &&
            !right.is_float &&
            right.integer < 0) {
            set_error(p, p->file_offset + exponent_start + 1);
            return left;
        }

        double result = pow(number_value(left), number_value(right));

        if (!isfinite(result)) {
            set_error(p, p->file_offset + operator_position + 1);
            return left;
        }

        if (!left.is_float && !right.is_float) {
            if (right.integer >= 0 &&
                right.integer <= 63) {

                long long result_integer = 1;

                for (long long i = 0; i < right.integer; i++) {
                    result_integer *= left.integer;
                }

                return make_integer(result_integer, left.start);
            }

            return make_float(result, left.start);
        }

        return make_float(result, left.start);
    }

    return left;
}

/* ---------- Multiplication and division ---------- */

static Number parse_term(Parser *p)
{
    Number left = parse_power(p);

    while (!p->failed) {
        skip_spaces(p);

        if (p->position >= p->length) {
            break;
        }

        char op = p->text[p->position];

        if (op != '*' && op != '/') {
            break;
        }

        if (op == '*' &&
            p->position + 1 < p->length &&
            p->text[p->position + 1] == '*') {
            break;
        }

        p->position++;

        skip_spaces(p);

        size_t right_start = p->position;

        if (p->position >= p->length) {
            set_error_at_end(p);
            break;
        }

        if (p->text[p->position] == ')' ||
            p->text[p->position] == '+' ||
            p->text[p->position] == '-' ||
            p->text[p->position] == '*' ||
            p->text[p->position] == '/') {
            set_error_here(p);
            break;
        }

        Number right = parse_power(p);

        if (p->failed) {
            break;
        }

        if (op == '/') {
            if (number_value(right) == 0.0) {
                set_error(p, p->file_offset + right_start + 1);
                break;
            }

            if (!left.is_float && !right.is_float) {
                left.integer /= right.integer;
                left.floating = (double)left.integer;
            } else {
                left.floating =
                    number_value(left) / number_value(right);
                left.is_float = 1;
            }
        } else {
            if (!left.is_float && !right.is_float) {
                left.integer *= right.integer;
                left.floating = (double)left.integer;
            } else {
                left.floating =
                    number_value(left) * number_value(right);
                left.is_float = 1;
            }
        }

        if (!isfinite(number_value(left))) {
            set_error(p, p->file_offset + right_start + 1);
            break;
        }

        left.is_float = left.is_float || right.is_float;
    }

    return left;
}

/* ---------- Addition and subtraction ---------- */

static Number parse_expression(Parser *p)
{
    Number left = parse_term(p);

    while (!p->failed) {
        skip_spaces(p);

        if (p->position >= p->length) {
            break;
        }

        char op = p->text[p->position];

        if (op != '+' && op != '-') {
            break;
        }

        p->position++;

        skip_spaces(p);

        if (p->position >= p->length) {
            set_error_at_end(p);
            break;
        }

        if (p->text[p->position] == ')' ||
            p->text[p->position] == '+' ||
            p->text[p->position] == '-' ||
            p->text[p->position] == '*' ||
            p->text[p->position] == '/') {
            set_error_here(p);
            break;
        }

        Number right = parse_term(p);

        if (p->failed) {
            break;
        }

        if (!left.is_float && !right.is_float) {
            if (op == '+') {
                left.integer += right.integer;
            } else {
                left.integer -= right.integer;
            }

            left.floating = (double)left.integer;
        } else {
            if (op == '+') {
                left.floating =
                    number_value(left) + number_value(right);
            } else {
                left.floating =
                    number_value(left) - number_value(right);
            }

            left.is_float = 1;
        }

        left.is_float = left.is_float || right.is_float;
    }

    return left;
}

/* ---------- Evaluate the whole input file ---------- */

static int evaluate_file(const char *input,
                        StringBuffer *results,
                        size_t *error_position)
{
    size_t input_length = strlen(input);
    size_t line_start = 0;

    while (line_start < input_length) {
        size_t line_end = line_start;

        while (line_end < input_length &&
               input[line_end] != '\n') {
            line_end++;
        }

        size_t line_length = line_end - line_start;
        int has_newline = line_end < input_length;

        Parser line;

        line.text = input + line_start;
        line.length = line_length;
        line.position = 0;
        line.file_offset = line_start;
        line.error_position = 0;
        line.failed = 0;
        line.line_end_position = line_end + 1;

        skip_spaces(&line);

        if (line.position == line.length ||
            line.text[line.position] == '#') {
            line_start = has_newline ? line_end + 1 : line_end;
            continue;
        }

        Number result = parse_expression(&line);

        skip_spaces(&line);

        if (!line.failed && line.position < line.length) {
            set_error_here(&line);
        }

        if (line.failed) {
            *error_position = line.error_position;
            return 0;
        }

        char output_line[128];

        if (result.is_float) {
            snprintf(output_line, sizeof(output_line),
                     "%.15g\n", result.floating);
        } else {
            snprintf(output_line, sizeof(output_line),
                     "%lld\n", result.integer);
        }

        if (!buffer_append_line(results, output_line)) {
            return 0;
        }

        line_start = has_newline ? line_end + 1 : line_end;
    }

    return 1;
}

/* ---------- File and path helpers ---------- */

static char *read_file(const char *path)
{
    FILE *file = fopen(path, "rb");

    if (file == NULL) {
        return NULL;
    }

    if (fseek(file, 0, SEEK_END) != 0) {
        fclose(file);
        return NULL;
    }

    long size = ftell(file);

    if (size < 0) {
        fclose(file);
        return NULL;
    }

    rewind(file);

    char *data = malloc((size_t)size + 1);

    if (data == NULL) {
        fclose(file);
        return NULL;
    }

    size_t read_count = fread(data, 1, (size_t)size, file);
    data[read_count] = '\0';

    fclose(file);

    return data;
}

static int make_directory(const char *path)
{
    struct stat st;

    if (stat(path, &st) == 0) {
        return S_ISDIR(st.st_mode);
    }

    return mkdir(path, 0777) == 0;
}

static const char *base_name(const char *path)
{
    const char *slash = strrchr(path, '/');

    return slash == NULL ? path : slash + 1;
}

static void remove_txt_extension(char *name)
{
    size_t length = strlen(name);

    if (length >= 4 &&
        strcmp(name + length - 4, ".txt") == 0) {
        name[length - 4] = '\0';
    }
}

/* ---------- Process one input file ---------- */

static int process_file(const char *input_path,
                       const char *output_dir)
{
    char *input = read_file(input_path);

    if (input == NULL) {
        perror(input_path);
        return 0;
    }

    StringBuffer results;
    results.data = NULL;
    results.length = 0;
    results.capacity = 0;

    size_t error_position = 0;

    int success = evaluate_file(input, &results, &error_position);

    char output_path[2048];
    char input_name[1024];

    snprintf(input_name, sizeof(input_name), "%s",
             base_name(input_path));

    remove_txt_extension(input_name);

    snprintf(output_path, sizeof(output_path),
             "%s/%s_%s_%s_%s.txt",
             output_dir,
             input_name,
             FIRST_NAME,
             LAST_NAME,
             STUDENT_ID);

    FILE *output = fopen(output_path, "w");

    if (output == NULL) {
        perror(output_path);
        free(input);
        free(results.data);
        return 0;
    }

    if (!success) {
        fprintf(output, "ERROR:%zu\n", error_position);
    } else if (results.data != NULL) {
        fwrite(results.data, 1, results.length, output);
    }

    fclose(output);

    free(input);
    free(results.data);

    return 1;
}

/* ---------- Main: command line options ---------- */

int main(int argc, char *argv[])
{
    const char *input_file = NULL;
    const char *input_dir = NULL;
    const char *output_dir = NULL;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-d") == 0 ||
            strcmp(argv[i], "--dir") == 0) {

            if (i + 1 >= argc) {
                fprintf(stderr, "Missing directory argument\n");
                return 1;
            }

            input_dir = argv[++i];

        } else if (strcmp(argv[i], "-o") == 0 ||
                   strcmp(argv[i], "--output-dir") == 0) {

            if (i + 1 >= argc) {
                fprintf(stderr, "Missing output directory argument\n");
                return 1;
            }

            output_dir = argv[++i];

        } else if (argv[i][0] == '-') {
            fprintf(stderr, "unknown option: %s\n", argv[i]);
            return 1;

        } else {
            if (input_file != NULL) {
                fprintf(stderr, "Only one input file is allowed\n");
                return 1;
            }

            input_file = argv[i];
        }
    }

    if (input_file == NULL && input_dir == NULL) {
        fprintf(stderr,
                "Usage: calc [-d DIR] [-o OUTDIR] [input.txt]\n");
        return 1;
    }

    char default_output_dir[2048];

    if (output_dir == NULL) {
        const char *source_name;

        if (input_file != NULL) {
            source_name = base_name(input_file);
        } else {
            source_name = base_name(input_dir);
        }

        char source_copy[1024];

        snprintf(source_copy, sizeof(source_copy), "%s", source_name);
        remove_txt_extension(source_copy);

        snprintf(default_output_dir, sizeof(default_output_dir),
                 "%s_%s_%s",
                 source_copy,
                 FIRST_NAME,
                 STUDENT_ID);

        output_dir = default_output_dir;
    }

    if (!make_directory(output_dir)) {
        fprintf(stderr, "Cannot create output directory: %s\n",
                output_dir);
        return 1;
    }

    if (input_file != NULL) {
        return process_file(input_file, output_dir) ? 0 : 1;
    }

    DIR *dir = opendir(input_dir);

    if (dir == NULL) {
        perror(input_dir);
        return 1;
    }

    struct dirent *entry;
    int success = 1;

    while ((entry = readdir(dir)) != NULL) {
        size_t length = strlen(entry->d_name);

        if (length < 4 ||
            strcmp(entry->d_name + length - 4, ".txt") != 0) {
            continue;
        }

        char input_path[2048];

        snprintf(input_path, sizeof(input_path),
                 "%s/%s", input_dir, entry->d_name);

        struct stat st;

        if (stat(input_path, &st) != 0 ||
            !S_ISREG(st.st_mode)) {
            continue;
        }

        if (!process_file(input_path, output_dir)) {
            success = 0;
        }
    }

    closedir(dir);

    return success ? 0 : 1;
}