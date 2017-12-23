#include <stdio.h>
#include <string.h>   /* for all the new-fangled string functions */
#include <stdlib.h>   /* malloc, free, rand */

struct tableau {
    char* root;
    struct  tableau* left;
    struct tableau* right;
    struct tableau* parent;
} *tab, *node, *node1, *kid, *pa;

void printTableau(struct tableau* t);
char* getSubformulaOf(char* g, int start, int length);
int getBinaryConnectiveOf(char* g);
int parse(char* g);
int lengthOf(char* g);
void complete(struct tableau* t);
int closed(struct tableau* t);
char* negate(char* formula);
void addFormulaBelow(struct tableau* parent, int direction, struct tableau* node, char* formula);
int typeOfBinaryFormula(char* g);
char* reduceNegations(char* g);

int Fsize=50;
int cases=10;

int i;
int j;

// FOR DEBUGGING
void printTableau(struct tableau* t) {
    if (t == NULL) { printf("nil"); return; }
    if (t->root == NULL) { printf("root nil"); return; }
    printf("%s { ", t->root);
    printTableau(t->left);
    printf(", ");
    printTableau(t->right);
    printf(" }");
    return;
}

void complete(struct tableau* t) {

    if (t == NULL) return;

    int type = parse(t->root);

    // Multiple negations (Alpha case)
    if ((type == 2) && (t->root[1] == '-')) {  // --p
        t->root = reduceNegations(t->root);
        complete(t);
        return;
    }

    int length = lengthOf(t->root)-1;
    char* negatedSubformula = getSubformulaOf(t->root, 1, length);

    // Proposition or negated proposition
    if ((type == 1) || ((type == 2) && (parse(negatedSubformula) == 1))) {
      complete(t->left);
      complete(t->right);
      return;
    }

    int indexBC = getBinaryConnectiveOf(t->root);
    char* firstFormula;
    char* secondFormula = getSubformulaOf(t->root, indexBC+1, length-1);
    if (t->root[0] != '-') firstFormula = getSubformulaOf(t->root, 1, indexBC-1);
    else firstFormula = getSubformulaOf(t->root, 2, indexBC-1);

    // Alpha Formulas
    if ((type == 3) && (typeOfBinaryFormula(t->root) == 2)) {  // p^p
        addFormulaBelow(NULL, -1, t, firstFormula);
        addFormulaBelow(NULL, -1, t, secondFormula);
    } if ((type == 2) && (typeOfBinaryFormula(negatedSubformula) == 3)) {  // -(p>p)
        addFormulaBelow(NULL, -1, t, firstFormula);
        addFormulaBelow(NULL, -1, t, negate(secondFormula));
    } if ((type == 2) && (typeOfBinaryFormula(negatedSubformula) == 1)) {  // -(pvp)
        addFormulaBelow(NULL, -1, t, negate(firstFormula));
        addFormulaBelow(NULL, -1, t, negate(secondFormula));
    }

    // Beta Formulas
    if ((type == 3) && (typeOfBinaryFormula(t->root) == 1)) {  // pvp
        addFormulaBelow(t, 0, t->left, firstFormula);
        addFormulaBelow(t, 1, t->right, secondFormula);
    } if ((type== 3) && (typeOfBinaryFormula(t->root) == 3)) {  // p>p
        addFormulaBelow(t, 0, t->left, negate(firstFormula));
        addFormulaBelow(t, 1, t->right, secondFormula);
    } if ((type == 2) && (typeOfBinaryFormula(negatedSubformula) == 2)) {  // -(p^p)
        addFormulaBelow(t, 0, t->left, negate(firstFormula));
        addFormulaBelow(t, 1, t->right, negate(secondFormula));
    }

    complete(t->left);
    complete(t->right);

    return;
}

// Assuming the negations have been reduced (no --p)
char* negate(char* formula) {

    char* negated = malloc(Fsize+1);
    int i, type = parse(formula), length = lengthOf(formula);

    if (type == 2) {
        for (i=1; i<length; i++) {
            negated[i-1] = formula[i];
        }
    }

    else {
        negated[0] = '-';
        for (i=0; i<length; i++) {
            negated[i+1] = formula[i];
        }
    }

    return negated;
}

// Add in every leaf
// Direction: 0=left, 1=right, -1=null (if parent is null)
void addFormulaBelow(struct tableau* parent, int direction, struct tableau* node, char* formula) {

  if (node == NULL) {
    struct tableau* newNode = malloc(sizeof(struct tableau));
    newNode->root = formula; newNode->right = NULL; newNode->left = NULL; newNode->parent = parent;
    node = newNode;
    if (direction == 0) {
      parent->left = node;
    } else if (direction == 1) {
      parent->right = node;
    }
    return;
  }

  addFormulaBelow(node, 0, node->left, formula);
  addFormulaBelow(node, 1, node->right, formula);

  return;
}

int typeOfBinaryFormula(char* g) {

    int indexBC = getBinaryConnectiveOf(g);

    if (g[indexBC] == 'v') return 1;
    if (g[indexBC] == '^') return 2;
    if (g[indexBC] == '>') return 3;

    return 0;
}

char* reduceNegations(char* g) {

    char *reduced = malloc(Fsize+1);
    int i, negations = 0, negated = 1, reducedLength = 0, length = lengthOf(g);

    if (g[0] != '-') {
        return g;
    }

    for (i=0; i<length; i++) {
        if (g[i] == '-') {
            if (negations == 0) {
                negations++;
            }
            else if (negations % 2 != 0) {
                negated = 0;
                negations++;
            }
            else {
                negated = 1;
                negations++;
            }
        }
        else {
            if ((g[i-1] == '-') && negated == 1) {
                reduced[0] = '-';
                reduced[1] = g[i];
                reducedLength += 2;
            } else if (negated == 1) {
                reduced[reducedLength] = g[i];
                reducedLength++;
            }
        }
    }

    return reduced;
}

int areEqual(char* first, char* second) {
  int i, length = lengthOf(first);
  if (length != lengthOf(second)) return 0;
  for(i=0; i<length; i++) {
    if (first[i] != second[i]) return 0;
  }
  return 1;
}

int findNegationOf(char* p, struct tableau* t) {
  if (t == NULL) return 0;
  if (areEqual(t->root, negate(p)) == 1) return 1;
  return (findNegationOf(p, t->right) || findNegationOf(p, t->left));
}

int closed(struct tableau* t) {

    if (t == NULL) {
      return 0; // I am not sure about this
    }

    if (lengthOf(t->root) < 3) {
      if (findNegationOf(t->root, t) == 1) return 1;
    }

    if ((t->right != NULL) && (t->left != NULL)) return (closed(t->right) && closed(t->left));
    if (t->right != NULL) return closed(t->right);
    if (t->left != NULL) return closed(t->left);

    return 0; // Should not happen
}

int parse(char* g) {
    int length = lengthOf(g)-1; // -1 is for easier call of getSubformulaOf()
    if (length == 0 && ((g[0] == 'p') || (g[0] == 'q') || (g[0] == 'r')))
        return 1;
    else if ((g[0] == '-') && (parse(getSubformulaOf(g, 1, length)) != 0))
        return 2;
    else if (g[0] == '(') {
        int indexBC = getBinaryConnectiveOf(g);
        if (indexBC != 0) {
            if ((parse(getSubformulaOf(g, 1, indexBC-1)) != 0) && (parse(getSubformulaOf(g, indexBC+1, length-1)) != 0)) return 3;
        }
    }

    return 0; // If none of the above
}

char* getSubformulaOf(char* g, int start, int length) {
    char *formula = malloc(Fsize+1);
    int i;
    for (i=0; i<=(length-start); i++) {
        formula[i] = g[start+i];
    }

    return formula;
}

int getBinaryConnectiveOf(char* g) {
    int len = lengthOf(g)-1; // -1 to not read the parenthesis
    int i, leftPar = 0, rightPar;
    if (g[0] == '-') rightPar = 1;
    else rightPar = 0;
    for (i=1; i<len; i++) {
        if ((g[i] == '>' || g[i] == 'v' || g[i] == '^') && leftPar == rightPar)
            return i;
        else if (g[i] == '(')
            leftPar++;
        else if (g[i] == ')')
            rightPar++;
    }

    return 0;
}

int lengthOf(char* g) {
    int c = 0;
    while(*g != '\0') {
        c++;
        g++;
    }

    return(c);
}

int main() {

    char *name = malloc(Fsize);
    FILE *fp, *fpout;

    /* reads from input.txt, writes to output.txt*/
    if ((fp=fopen("input.txt","r"))==NULL) { printf("Error opening file"); exit(1); }
    if ((fpout=fopen("output.txt","w"))==NULL) { printf("Error opening file"); exit(1); }

    int j;
    for(j=0; j<cases; j++) {
        fscanf(fp, "%s", name);/*read formula*/
        switch (parse(name)) {
            case(0): fprintf(fpout, "%s is not a formula.  ", name);break;
            case(1): fprintf(fpout, "%s is a proposition.  ", name);break;
            case(2): fprintf(fpout, "%s is a negation.  ", name);break;
            case(3): fprintf(fpout, "%s is a binary.  ", name);break;
            default: fprintf(fpout, "What the f***!  ");
        }

        /*make new tableau with name at root, no children, no parent*/
        struct tableau t = {name, NULL, NULL, NULL};

        /*expand the root, recursively complete the children*/
        if (parse(name) != 0) {
            complete(&t);
            if (closed(&t)) fprintf(fpout, "%s is not satisfiable.\n", name);
            else fprintf(fpout, "%s is satisfiable.\n", name);
        }
        else fprintf(fpout, "I told you, %s is not a formula.\n", name);
    }

    fclose(fp);
    fclose(fpout);
    free(name);

    return(0);
}
