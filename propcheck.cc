/*
* propcheck <filename>
* Author: Pradu Kannan
* Date: Sun Jun 10 16:49:21 MST 2018
*
* Automatically checks statements made in propositional logic.
*
* Every line except the last line are axioms.
* The last line is the theorem to prove.
* Up to 32 variables can be used.
*
* Notation for Propositions:
*    A variable       [A string inside square brackets]
*    Implication      ( [A] => [B]  )     ( [A] implies [B] )     ( [A] then [B] )
*    Implication      ( [A] <= [B]  )     ( [A] if [B] )
*    If and only if   ( [A] <=> [B] )     ( [A] iff [B]     )
*    And              ( [A] & [B]   )     ( [A] and [B]     )
*    Or               ( [A] | [B]   )     ( [A] or [B]      )
*    Xor              ( [A] ^ [B]   )     ( [A] xor [B]     )
*    Not              ![A]                not [A]
*    True             T                   true
*    False            F                   false
*/

#include <memory>
#include <cstdio>
#include <cstdlib>
#include <cctype>
#include <vector>
#include <string>

using namespace std;

typedef unsigned long U32;
typedef unsigned long BOOL;

//An Expression Type
struct Expr
{
    virtual BOOL operator()(U32 x) = 0;
};

//True and False Expressions
struct True: public Expr
{
    BOOL operator()(U32 x) { return BOOL(1); }
};
struct False: public Expr
{
    BOOL operator()(U32 x) { return BOOL(0); }
};

//A Variable Expression
struct Var : public Expr
{
    BOOL shift;
    Var(BOOL shift_in) : shift(shift_in) {};
    BOOL operator()(U32 x) { return ((x>>shift) & 1); }
};

//A Not Expression
struct Not : public Expr
{
    shared_ptr<Expr> E; //Left Expression
    Not(shared_ptr<Expr> E_in) : E(E_in) {};
    BOOL operator()(U32 x) { return (BOOL(1)^((*E)(x))); }
};

//Various Binary Expressions
struct And : public Expr
{
    shared_ptr<Expr> L; //Left Expression
    shared_ptr<Expr> R; //Right Expression
    And(shared_ptr<Expr> L_in, shared_ptr<Expr> R_in) : L(L_in), R(R_in) {};
    BOOL operator()(U32 x) { return ((*L)(x)) & ((*R)(x)); }
};
struct Or : public Expr
{
    shared_ptr<Expr> L; //Left Expression
    shared_ptr<Expr> R; //Right Expression
    Or(shared_ptr<Expr> L_in, shared_ptr<Expr> R_in) : L(L_in), R(R_in) {};
    BOOL operator()(U32 x) { return ((*L)(x)) | ((*R)(x)); }
};
struct Xor : public Expr
{
    shared_ptr<Expr> L; //Left Expression
    shared_ptr<Expr> R; //Right Expression
    Xor(shared_ptr<Expr> L_in, shared_ptr<Expr> R_in) : L(L_in), R(R_in) {};
    BOOL operator()(U32 x) { return ((*L)(x)) ^ ((*R)(x)); }
};
struct Implies : public Expr
{
    shared_ptr<Expr> L; //Left Expression
    shared_ptr<Expr> R; //Right Expression
    Implies(shared_ptr<Expr> L_in, shared_ptr<Expr> R_in) : L(L_in), R(R_in) {};
    BOOL operator()(U32 x) { return (BOOL(1))^(((*L)(x)) & ((BOOL(1))^((*R)(x))) ); }
};
struct Iff : public Expr
{
    shared_ptr<Expr> L; //Left Expression
    shared_ptr<Expr> R; //Right Expression
    Iff(shared_ptr<Expr> L_in, shared_ptr<Expr> R_in) : L(L_in), R(R_in) {};
    BOOL operator()(U32 x) { return ((*L)(x))==((*R)(x)); }
};

//Expression Parsing
U32 parseExpr(const char* s, shared_ptr<Expr>& p);

U32 skipWS(const char* s) //skip Whitespace
{
    const char* e = s;
    while( isspace(*e) ) e++;
    return (U32)(e-s);
}

U32 parseString(const char* s, const char* str)
{
    const char* e=s;
    while(*str!='\0' && *e!='\0' && *e==*str)
    {
        e++;
        str++;
    }
    if( *str=='\0' )
        return U32(e-s);
    return U32(0);
}

U32 parseOneString(const char* s, const char* str1, const char* str2)
{
    U32 n = parseString(s,str1);
    if( n )
        return n;
    return parseString(s,str2);
}

U32 parseTrue(const char* s, shared_ptr<Expr>& p)
{
    if( *s=='T' )
    {
        p = shared_ptr<Expr>(new True);
        return 1;
    }
    U32 n = parseString(s,"true");
    if(n)
        p = shared_ptr<Expr>(new True);
    return n;
}

U32 parseFalse(const char* s, shared_ptr<Expr>& p)
{
    if( *s=='F' )
    {
        p = shared_ptr<Expr>(new False);
        return 1;
    }
    U32 n = parseString(s,"false");
    if(n)
        p = shared_ptr<Expr>(new False);
    return n;
}

vector<string> variables; //Global for simplicity
U32 parseVar(const char* s, shared_ptr<Expr>& p)
{
    const char* e=s;
    if( *e!='[' )
        return U32(0);
    e++;
    e+=skipWS(e);
    char const* startstr = e;
    while( *e!=']' )
    {
        if( *e=='\0' )
            return U32(0);
        e++;
    }
    e--;
    while( isspace(*e) && e > startstr ) e--;
    e++;
    string var(startstr,string::size_type(e-startstr));
    while( *e!=']' ) e++;
    e++;

    {
        int i;
        for(i=0; i<variables.size(); i++)
            if( variables[i] == var )
                break;
        if( i >= variables.size() )
            variables.push_back(var);
        if( variables.size() > 32 )
        {
            printf("error: over 32 propositional variables, Exitting.\n");
            exit(1);
        }
        p = shared_ptr<Expr>(new Var(i));
    }
    return U32(e-s);
}

U32 parseNot(const char* s, shared_ptr<Expr>& p)
{
    const char* e = s;
    U32 n = parseOneString(s,"!","not");
    if(n)
    {
        e+=n;
        shared_ptr<Expr> L;
        n=parseExpr(e,L);
        if( n )
        {
            e+=n;
            p=shared_ptr<Expr>(new Not(L));
            return U32(e-s);
        }
    }
    return 0;
}

U32 parseBinaryExpr(const char* s, shared_ptr<Expr>& p)
{
    U32 n;
    const char* e = s;
    e += skipWS(e);
    if( *e!='(' )
        return 0;
    e++;

    //Parse Left Expression
    e += skipWS(e);
    shared_ptr<Expr> L;
    n = parseExpr(e,L);
    if(!n)
        return 0;
    e += n;

    //Parse Operation String
    e+=skipWS(e);
    const char* startop = e;
    while( *e!='\0' && *e!='!' && *e!='(' && *e!='[' &&
           *e!='T' && *e!='F' && (*e!='f' || *(e+1)!='a' ) && (*e!='t' || *(e+1)!='r') &&
           (*e!='n' || *(e+1)!='o') && !isspace(*e) ) e++;
    string op(startop,e-startop);
    e+=skipWS(e);

    //Parse Right Expression
    e += skipWS(e);
    shared_ptr<Expr> R;
    n = parseExpr(e,R);
    if(!n)
        return 0;
    e += n;

    //Parse Closing Parenthesis
    e += skipWS(e);
    if( *e!=')' )
        return 0;
    e++;

    if( op=="and" || op=="&" )
    {
        p = shared_ptr<Expr>(new And(L,R));
        return U32(e-s);
    }
    if( op=="or" || op=="|" )
    {
        p = shared_ptr<Expr>(new Or(L,R));
        return U32(e-s);
    }
    if( op=="xor" || op=="^" )
    {
        p = shared_ptr<Expr>(new Xor(L,R));
        return U32(e-s);
    }
    if( op=="then" || op=="implies" || op=="=>" )
    {
        p = shared_ptr<Expr>(new Implies(L,R));
        return U32(e-s);
    }
    if( op=="if" || op=="<=" )
    {
        p = shared_ptr<Expr>(new Implies(R,L));
        return U32(e-s);
    }
    if( op=="iff" || op=="<=>" )
    {
        p = shared_ptr<Expr>(new Iff(L,R));
        return U32(e-s);
    }

    return 0;
}

U32 parseExpr(const char* s, shared_ptr<Expr>& p)
{
    U32 n;
    const char* e = s;
    e += skipWS(e);
    if( n=parseTrue(e,p) )
    {
        e += n;
        return  U32(e-s);
    }
    if( n=parseFalse(e,p) )
    {
        e += n;
        return  U32(e-s);
    }
    else if( n=parseVar(e,p) )
    {
        e += n;
        return  U32(e-s);
    }
    else if( n=parseNot(e,p) )
    {
        e += n;
        return  U32(e-s);
    }
    else if( n=parseBinaryExpr(e,p) )
    {
        e += n;
        return  U32(e-s);
    }
    return 0;
}

U32 parseTopLevelExpr(const char* s, shared_ptr<Expr>& p)
{
    char const* e = s;
    U32 n = parseExpr(e,p);
    e += n;
    e += skipWS(e);
    if( n && *e=='\0' )
        return U32(e-s);

    //Attempt to add parenthesis to expression and parse again
    std::string test=(std::string("(")+s+")");
    e = test.c_str();
    n = parseExpr(e,p);
    e += n;
    e += skipWS(e);
    if( n && *e=='\0' )
        return U32(e-s);

    return 0;
}

int main(int argc, char* argv[])
{
    vector<shared_ptr<Expr>> propositions;
    if( argc<2 )
    {
        printf("Usage: propcheck <filename>\n");
        return 1;
    }

    FILE* f = fopen(argv[1],"rb");
    if(!f)
    {
        printf("Error: Cannot open %s\n", argv[1]);
        return 1;
    }
    char line[8192*2];
    unsigned long linenum = 0;
    while(fgets(line,8192*2,f))
    {
        linenum++;
        if(line[0]=='/' && line[1]=='/') //Skip Comments
            continue;
        if(*(line+skipWS(line))=='\0') //Skip Empty lines
            continue;
        shared_ptr<Expr> p;
        if(!parseTopLevelExpr(line,p))
        {
            printf("Error: Syntax Error line %lu in %s\n",linenum,argv[1]);
            return 1;
        }
        propositions.push_back(p);
    }
    fclose(f);

    if( propositions.size()<1 )
    {
        printf("Error: No theorem to check in %s\n",argv[1]);
        return 1;
    }

    U32 max = 1;
    for( int i=1; i<variables.size(); i++ )
    {
        max|=(1<<i);
    }

    bool axiomsConsistent = false;
    for( U32 x=0; x<=max; x++ )
    {
        //Check Axioms
        int i;
        for( i=0; i<propositions.size()-1; i++ )
            if( !(*propositions[i])(x) ) //if axiom is not true
                break;
        if( i!=propositions.size()-1 ) //axioms not satisfied
            continue;
        axiomsConsistent = true;
        if( !(*propositions[i])(x) ) //if theorem is not satisfied, we have a counterexample
        {
            printf("Theorem is false!\n");
            if(variables.size()>=1)
            {
                printf("Counterexample:\n");
                printf("%40s Value\n","Proposition");
            }
            for(U32 j=0; j<variables.size(); j++)
            {
                if( (U32(1)<<j)&x )
                    printf("%40s True\n",variables[j].c_str());
                else
                    printf("%40s False\n",variables[j].c_str());
            }
            return 1;
        }
    }

    if( !axiomsConsistent )
        printf("Axioms are not consistent!\n");
    else
        printf("Theorem has veen verified!\n");

    //Debugging: Printing 2-Variable Truth Tables
    //shared_ptr<Expr> p;
    //if(parseTopLevelExpr("[P] and not [P]",p))
    //{
    //    for(U32 x=0; x<4; x++ )
    //        printf("p %d => %d\n", x, (*p)(x));
    //}
    return 0;
}
