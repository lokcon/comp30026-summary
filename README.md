# Lecture Slides
## Propositional Logic
* Well-formed formulas (wffs) for Propositional Logic
    * `wff -> A | B | C ...| Z | f | t`
        * `| (¬wff)`
        * `| (wff ∧ wff)`
        * `| (wff ∨ wff)`
        * `| (wff ⇒ wff)`
        * `| (wff ⇔ wff)`
        * `| (wff ⊕ wff)`
* `¬` binds tighter than `∧` and `∨`, tighter than `(xor)`, tighter than `⇒` and ⇔
* **Truth assignment** maps each propositional letter to `t` or `f`
* **Semantics** of connectives shown by **truth table**
* **Conjunction** `P ∧ Q`
* **Disjunction** `P ∨ Q`
* **Implication**` P ⇒ Q ≡ ¬P ∨ Q`
* **Contrapositive** `P ⇒ Q ≡ ¬Q ⇒ P`

## Logic Concepts
* **Valid** (**tautology**) - no truth assignment makes it false, otherwise **non-valid**
* **Unsatisfiable** (**contradiction**) - no truth assignment makes it true, otherwise **satisfiable**
* **Substitution** of propositional letters by formulas preverses **validity** and **unsatisfiability** (but not **satisfiablity**)
    * Not satisfiablity and non-validity
* A formula is **unsatisfiable iff** its **negation** is **valid**
* θ is a **model** of Φ: θ truth assignment makes propositional formula Φ true
* Ψ is a **logical consequence** of Φ `Φ |= Ψ` iff every model of Φ is a model of Ψ
* **Equivalence:** `Φ |= Ψ` and `Ψ |= Φ`, `Φ ≡ Ψ`
* **Substitution** (between logically equivalent formulas) preverses **logical equivalence**
* **Interchange of equivalents** preserves **logical equivalence**, **logical consequence**, **validity**, **satisfiability**
* Equivalences
    * **Absorption:** `P ∧ P ≡ P` `P ∨ P ≡ P`
    * **Commutativity:** `P ∧ Q ≡ Q ∧ P` `P ∨ Q ≡ Q ∨ P`
    * **Associativity:** `P ∧ (Q ∧ R) ≡ (P ∧ Q) ∧ R` `P ∨ (Q ∨ R) ≡ (P ∨ Q) ∨ R`
    * **Distributivity:** `P ∧ (Q ∨ R) ≡ (P ∧ Q) ∨ (P ∧ R)` `P ∨ (Q ∧ R) ≡ (P ∨ Q) ∧ (P ∨ R)`
        * ⇔ and ⊕ are also commutative and associative.
    * **Double negation:** `P ≡ ¬¬P`
    * **De Morgan:** `¬(P ∧ Q) ≡ ¬P ∨ ¬Q` `¬(P ∨ Q) ≡ ¬P ∧ ¬Q`
    * **Implication:** `P ⇒ Q ≡ ¬P ∨ Q`
    * **Contraposition:** `¬P ⇒ ¬Q ≡ Q ⇒ P` `P ⇒ ¬Q ≡ Q ⇒ ¬P` `¬P ⇒ Q ≡ ¬Q ⇒ P`
    * **Biimplication:** P ⇔ Q ≡ (P ∧ Q) ∨ (¬P ∧ ¬Q)
* Let `⊥` be any unsatisfiable formula and let `⊤` be any valid formula.
    * **Duality:** `¬⊤ ≡ ⊥` `¬⊥ ≡ ⊤`
    * **Negation from absurdity:** `P ⇒ ⊥ ≡ ¬P`
    * **Identity:** `P∨⊥≡ P` `P∧⊤≡ P`
    * **Dominance:** `P∧⊥≡⊥` `P∨⊤≡⊤`
    * **Contradiction:** `P ∧ ¬P ≡ ⊥`
    * **Excluded middle:** `P ∨ ¬P ≡ ⊤`

## Mechanising Deduction
* **Propositional logic** is **deicdable**
* A **literal** is P or ¬P where P is a propositional letter.
* **CNF:** conjunction of disjuncitons of literals
* **DNF:** disjunction of conjuncitons of literals
* Normal forms are NOT unique
* Converting to CNF/DNF
    * Replace connectives with ∧ or ∨
    * De Morgan's law - push ¬ inward
    * Distrivitive law
* **Reduced CNF (RCNF):** No propositional letter occurs twice for each clause
* **Canonoical form**
    * **Xor Normal Form:** Unique
    * **Binary decision diagrams (BDDs)**
    * **Reduced ordered binary decision diagrams (ROBDDs)**
        * Valid iff ROBDD singale-leaf graph `t`
        * unsatisfiable `f`
* **Clausal form (CNF)**
    * Empty clause, `f`
    * Empty formula, `t`
* If R is a **resolvent** of C1 and C2, then `C1∧C2 |= R`
* **Resolution decution** (of set S of clauses)
    * `C1, C2 ...Cn`
    * `Cn = C`
    * `Ci` being
        * a member of `S`
        * `S` resolvent of `Cj` and `Ck` `(j, k < i)`
* **Resolution refutation** - Resolving set of clauses to `⊥`
* **Refutation**
    * Use **negation** when trying to show a set of clauses if valid
    * `Φ |= Ψ` iff `Φ ∧ ¬Ψ` is **unsatisfiable**

## Predicate: Syntax
* **Term:** *variable*, *constants*, or `f(t1, t2, ..., tn)`
* **Atomic formula:** `P(t1, t2, ..., tn)`
* **Literal:** *Atomic formula* or *its negation*
* `wff → atom`
    * `| ¬ wff`
    * `| wff ∧ wff`
    * `| wff ∨ wff`
    * `| wff ⇒ wff`
    * `| wff ⇔ wff`
    * `| wff ⊕ wff`
    * `| ∀var (wff)`
    * `| ∃var (wff)`
* **Variable:** *bound* or *free*

## Predicate: Semantics
* **Interpretation**
    * A non-empty set `D` (the **domain**, or universe);
    * An **assignment**, to each n-ary **predicate symbol** `P`, of a n-place function `p : D^n → {f, t}`
    * An **assignment**, to each n-ary **function symbol** `g` , of a n-place function `g : D^n → D`
    * An **assignment** to each **constant** a of some **fixed element** of `D`
* Free variables and valuations
    * A **valuation** `σ : Var → D` for free variables
    * `σ` for term from `σ : Var -> D` by **natural extension**
        * `σ(a) = d`
        * `σ(g (t1, ..., tn )) = g(σ(t 1 ), ..., σ(t n ))`
    * `σ(x|->d)` updated to map `x to d`
* **Model** for `F`: `I |= F`
* **Logically valid:** `|= F` every interpretation `I` is a model for `F`
* **Logical consequence** `F1 |= F2`
* **Logical equivanelt** `F1 ≡ F2`
* Rules of passage for quantifiers
    * `∃x (¬F1) ≡ ¬∀x F1`
    * `∀x (¬F1) ≡ ¬∃x F1`
    * `∃x (F1 ∨ F2) ≡ (∃x F1) ∨ (∃x F2)`
    * `∀x (F1 ∧ F2) ≡ (∀x F1) ∧ (∀x F2)`
* If G is a formula with no free occurrences of x, then we also get
    * `∃x G ≡ G`
    * `∀x G ≡ G`
    * `∃x (F ∧ G) ≡ (∃x F) ∧ G`
    * `∀x (F ∨ G) ≡ (∀x F) ∨ G`
    * `∀x (F ⇒ G) ≡ (∃x F) ⇒ G`
    * `∀x (G ⇒ F) ≡ G ⇒ (∀x F)`

## Predicate Logic: Clasual Form
* Convention
    * start of alphabet (a,b,c...) for constants
    * end of alphabet (u,v,x,y ...) for variables
    * middle of alphabet (f, g, h ...) for functions
* **Predicate logic formulas to Clasual form**
    * Replace occurrences of ⇒, ⇔, and ⊕
    * Drive negation in
    * Standardise bound variables apart
    * Eliminate existential quantifiers (**Skolemize**)
    * Eliminate universal quantifiers (just remove them)
    * Bring to CNF (using the distributive laws)
* Skolemization produce **equisatisfiable** formulas

## Predicate Logic: Unification and Resolution
* **Unifier** of two term s and t: `θ(s) = θ(t)`
* **Most general unifier (mgu)**:
    * `θ` is a unifier for `s` and `t`, and
    * every other unifier `σ` of `s` and `t` can be expressed as `τ ◦ θ` for some substitution `τ`
* **Theorem:** If s and t are unifiable, they have a most general unifier
* **Unification algorithm:**
    * `F(s1 , ..., s n ) = F (t1 , ..., tn )`
        * Replace the equation by the n equations `s1 = t1` , ..., `sn = tn`
    * `F(s1 , ..., sn) = G (t1 , ..., tm)` where `F != G` or `n != m`
        * Halt, returning ‘**failure**’.
    * `x = x`
        * Delete the equation.
    * `t = x` where `t` is not a variable
        * Replace the equation by x = t.
    * `x = t` where `t` is not `x` but `x` occurs in `t`
        * Halt, returning ‘**failure**’.
    * `x = t` where `t` contains no `x` but `x` occurs in other equations:
        * Replace `x` by `t` in those other equations.
* **Resolvent of two set of clauses:** Let `C1` and `C2` be clauses, renamed apart. Let `θ` be an mgu of complementary literals `{L, ¬L}` with `L` a literal in `C1` and `¬L` a literal in `C2` . Then the resolvent of `C1` and `C2` is the union `θ(C1 − {L}) ∪ θ(C2 − {¬L})`
* **Factoring:** Let `C` be a clause and let `A1 , A2 ∈ C` . If `A1` and `A2` are unifiable with mgu `θ`, add the clause `θ(C)`.

## Sets
* **Subset Relation** `A ⊆ B`: A is a subset of B iff `∀x (x ∈ A ⇒ x ∈ B)`
* **Proper subset** `A ⊂ B`: `A ⊆ B` and `A != B`
* **Intersection:** `A ∩ B` = `{x | x ∈ A ∧ x ∈ B}`
* **Union:** `A ∪ B` = `{x | x ∈ A ∨ x ∈ B}`
* **Difference:** `A \ B` = `{x | x ∈ A ∧ x ̸∈ B}`
* **Symmetric difference** `A ⊕ B` = `(A \ B) ∪ (B \ A)`
* **Complement:** `Ac = X \ A`
* Laws
    * **Absorption:** `A ∩ A = A` `A ∪ A = A`
    * **Commutativity:** `A ∩ B = B ∩ A` `A ∪ B = B ∪ A`
    * **Associativity:** `A ∩ (B ∩ C ) = (A ∩ B) ∩ C` `A ∪ (B ∪ C ) = (A ∪ B) ∪ C`
    * **Distributivity:** `A ∩ (B ∪ C ) = (A ∩ B) ∪ (A ∩ C)` `A ∪ (B ∩ C ) = (A ∪ B) ∩ (A ∪ C )`
    * **Double complement:** `A = (Ac) c`
    * **De Morgan:** `(A ∩ B) c = A c ∪ B c` `(A ∪ B) c = A c ∩ B c`
    * **Duality:** `X c = ∅` and `∅ c = X`
    * **Identity:** `A ∪ ∅ = A` and `A ∩ X = A`
    * **Dominance:** `A ∩ ∅ = ∅` and `A ∪ X = X`
    * **Complementation:** `A ∩ A c = ∅` and `A ∪ A c = X`
* Subset equivalences
    * Subset characterisation: `A ⊆ B ≡ A = A ∩ B ≡ B = A ∪ B`
    * Contraposition: `A c ⊆ B c ≡ B ⊆ A` `A ⊆ B c ≡ B ⊆ A c` `A c ⊆ B ≡ B c ⊆ A`
* **Powerset** `P(X)` = `{A | A ⊆ X }`
* **Generalised Union** `∪_ i∈I Ai` = `{x | ∃i ∈ I (x ∈ A i )}`
* Generalised Intersection `∩i∈I A i` = `{x | ∀i ∈ I (x ∈ A i )}`
* **Cartesian product**
    * `A × B = {(a, b) | a ∈ A ∧ b ∈ B}`
    * `A0 = {∅}, An+1 = A × An`
* Cartesian product Laws
    * `(A × B) ∩ (C × D) = (A × D) ∩ (C × B)`
    * `(A ∩ B) × C = (A × C ) ∩ (B × C )`
    * `(A ∪ B) × C = (A × C ) ∪ (B × C )`
    * `(A ∩ B) × (C ∩ D) = (A × C ) ∩ (B × D)`
    * `(A ∪ B) × (C ∪ D) = (A × C ) ∪ (A × D) ∪ (B × C ) ∪ (B × D)`
* **n-ary relation**
    * Subset of Cartesian product `A 1 × A 2 × · · · × A n`
    * Function from `A1 × A2 × ...× An to {0, 1}`

## Binary Relation and Functions
* Domain: dom(R) = {x | ∃y R(x, y )}
* Range: ran(R) = {y | ∃x R(x, y )}
* R is from A to B: dom(R) ⊆ A and ran(R) ⊆ B
* Some relations
    * Full relation: A × B
    * ∅
    * Identity relation: ∆A = {(x, x) | x ∈ A}
    * Inverse: R^(−1) = {(b, a) | R(a, b)}
* Properties of relations
    * R is reflexive iff R(x, x) for all x in A.
    * R is irreflexive iff R(x, x) holds for no x in A.
    * R is symmetric iff R(x, y ) ⇒ R(y , x) for all x, y in A.
    * R is asymmetric iff R(x, y ) ⇒ ¬R(y , x) for all x, y in A.
    * R is εmmetric iff R(x, y ) ∧ R(y , x) ⇒ x = y for all x, y in A.
    * R is transitive iff R(x, y ) ∧ R(y , z) ⇒ R(x, z) for all x, y , z in A.
* Reflexive, Symmetric, Transitive Closures
    * Transitive relations closed under intersection,
    * if R 1 and R 2 are transitive then so is R 1 ∩ R 2
    * R+ the transitive closure of R: smallest transitive relation R+ which includes R
    * Similar for reflexive closure and symmetric closure
* Composition
    * R1◦R2: (x, z) ∈ (R1 ◦ R2) iff ∃y (R1(x, y) ∧ R2 (y, z))
    * n-fold composition Rn
        * R1 = R
        * Rn+1 = Rn ◦ R
    * Transitive closure
        * R+ = ∪(n>=1) Rn
    * Reflexive, transitive closure
        * R∗ = ∪(n>=0) Rn = R+ ∪ ∆A
* Equivalence relations
    * A binary relation which is reflexive, symmetric and transitive is an
equivalence relation.
    * Smallest equivalence relation on A: identity relation ∆ A
    * Largest equivalence relation on A: full relation A2
* Partial Orders
    * R is a **pre-order** iff R is transitive and reflexive.
    * R is a **strict partial order** iff R is transitive and irreflexive.
    * R is a **partial order** iff R is an εmmetric preorder.
    * R is **linear** iff R(x, y) ∨ R(y, x) ∨ x = y for all x, y in A.
        * A linear partial order is also called a **total** order.
        * In a total order, every two elements from A are **comparable**.
* Functions
    * A function f is a relation with the property that (x, y ) ∈ f ∧ (x, z) ∈ f ⇒ y = z. That is, for x ∈ dom(f), there is exactly one y ∈ ran(f ) such that (x, y ) ∈ f . We write this: f (x) = y.
    * f: X → Y
        * dom(f) = X
        * ran(f) ⊆ Y
        * Y: co-domain of f
* Images and Co-images
    * f [A] = {f (x) | x ∈ A} is the image of A under f
    * f(−1)[B] = {x ∈ X | f (x) ∈ B} is the co-image of B under f
* Injections, Surjections and Bijections
    * A function f : X → Y is
        * surjective (or onto) iff f [X ] = Y .
        * injective (or one-to-one) iff f (x) = f (y ) ⇒ x = y .
        * bijective iff it is both surjective and injective.
* Function Composition
    * f : X → Y and g : Y → Z, g ◦ f : X → Z defined by (g ◦ f)(x) = g (f(x))
    * Is associative
    * f : X → Y, f ◦ 1X = 1Y ◦ f = f , where 1X : X → X is the identity function on X
    * g ◦ f injective ⇒ f injective;
    * g ◦ f surjective ⇒ g surjective;
    * g , f injective ⇒ g ◦ f injective;
    * g , f surjective ⇒ g ◦ f surjective.
* Partial functions: Not the whole of domain is defined

## Mathematical Proof
* Type of Proof
    * by construction
    * by contradiction
    * by induction
        * structural induction
* Type of statements
    * A conjecture is an unproven claim.
    * A theorem is a claim that has been proved true.
    * A lemma is a statement that is of interest only because it assists in the proof of a more significant statement.
    * A corollary is a simple consequence of a theorem.
    * A proposition is a more technical theorem, perhaps of les significance.
* Techniques
    * using contrapositive
    * to prove Φ ⇒ Ψ, start by supposing Φ holds
    * to prove Φ ⇔ Ψ, prove
    * to prove ∀x P(x), start by letting c be arbitrary
    * ...

## Finite State Automata
* δ is total function
* String: finite sequenice of symbols from Σ
* Concatenation: xy
* Empty string: denote by ε
* A finite automaton is a 5-tuple (Q, Σ, δ, q 0 , F ), where
    * Q is a finite set of states,
    * Σ is a finite alphabet,
    * δ : Q × Σ → Q is the transition function,
    * q0 ∈ Q is the start state, and
    * F ⊆ Q are the accept states.
* DFA Acceptance: M accepts w iff
    * sequence of states r 0 , r 1 , ..., r n ∈ Q
    * r 0 = q 0
    * δ(r i , v i +1 ) = r i +1 for i = 0, ..., n − 1
    * r n ∈ F
* An NFA is a 5-tuple (Q, Σ, δ, q 0 , F ), where
    * Q is a finite set of states,
    * Σ is a finite alphabet,
    * δ : Q × Σε → P(Q) is the transition function,
    * q0 ∈ Q is the start state, and
    * F ⊆ Q are the accept states.
* NFA Acceptance:
    * r 0 = q 0
    * r i +1 ∈ δ(r i , v i +1 ) for i = 0, ..., n − 1
    * r n ∈ F
* M recognises language A iff A = {w | M accepts w }
* Regular operations
    * Union: A U B
    * Concatentation: A ◦ B = {xy | x ∈ A, y ∈ B}
    * Kleene Star: A ∗ = {x 1 x 2 · · · x k | k ≥ 0, each x i ∈ A}
    * Regular languages are closed under these operations (by constructing NFA to recognise them)

## Regular Languages
* Can construct a DFA from NFA (up to 2^k states)
* Regular languages closed under
    * intersection,
    * complement, A c
    * difference (this follows, as A \ B = A ∩ B c )
    * reversal.
* (if) Compose each sub expressions of a regular expressions into small NFAs, then join all these NFAs together
    * (only if) Create a single end state, then apply state elemination process to create the regular expression
* Useful Laws
    * A ∪ A = A
    * A ∪ B = B ∪ A
    * (A ∪ B) ∪ C = A ∪ (B ∪ C )
    * (A ◦ B) ◦ C = A ◦ (B ◦ C )
    * ∅ ∪ A = A ∪∅ = A
    * ε ◦ A = A ◦ ε = A
    * ∅◦ A = A ◦∅ = ∅
    * (A ∪ B) ◦ C = A ◦ C ∪ B ◦ C
    * A ◦ (B ∪ C ) = A ◦ B ∪ A ◦ C
    * (A ∗ ) ∗ = A ∗
    * ∅ ∗ = ε ∗ = ε
    * (ε ∪ A) ∗ = A ∗
    * (A ∪ B) ∗ = (A ∗ B ∗ ) ∗
* Pumping Lemma: If A is regular then there is a number p such
that for any string s ∈ A with |s| ≥ p, s can be written as s = xyz,
satisfying
    * xy i z ∈ A for all i ≥ 0
    * y != ε
    * |xy| ≤ p

## Context-Free Languages
* A language which can be generated by some context-free grammar is
a context-free language
* A context-free grammar (CFG) G is a 4-tuple (V , Σ, R, S), where
    * V is a finite set of variables,
    * Σ is a finite set of terminals,
    * R is a finite set of rules, each consisting of a variable (the left-hand side) and a sentential form (the right-hand side),
    * S is the start variable.
* A grammar that has different parse trees for some sentence is
ambiguous.

## Pushdown Automata
* A pushdown automaton is a 6-tuple (Q, Σ, Γ, δ, q 0 , F ) where
    * Q is a finite set of states,
    * Σ is the finite input alphabet,
    * Γ is the finite stack alphabet,
    * δ : Q × Σ ε × Γ ε → P(Q × Γ ε ) is the transition function,
    * q0 ∈ Q is the start state, and
    * F ⊆ Q are the accept states.
* Acceptance w = v 1 v 2 · · · v n with each v i ∈ Σ ε , and there are states r 0 , r 1 , ..., r n ∈ Q and strings s 0 , s 1 , ..., s n ∈ Γ ∗ such that
* We can build a PDA
* Pumping Lemma: If A is context-free then there is a number p such that for any string s ∈ A with |s| ≥ p, s can be written as s = uvxyz, satisfying
    * uv i xy i z ∈ A for all i ≥ 0
    * |vy | > 0
    * |vxy | ≤ p
* Context-free languages closed under
    * Union
    * Concatentation
    * Kleeene Star
    * Reversal
    * NOT intersection
* A deterministic PDA is NOT as powerful as PDA

## Turing Machine
* A Turing machine is a 7-tuple M = (Q, Σ, Γ, δ, q 0 , q a , q r ) where
    * Q is a finite set of states,
    * Γ is a finite tape alphabet, which includes the blank character, xy,
    * Σ ⊆ Γ \ {xy} is the input alphabet,
    * δ : Q × Γ → Q × Γ × {L, R} is the transition function,
    * q0 is the initial state,
    * qa is the accept state, and
    * qr (6 = q a ) is the reject state.
* M accepts w iff there is a sequence of configurations C 1 , C 2 , ..., C k such that
    * C 1 is the start configuration q 0 w ,
    * C i ⇒ C i +1 for all i ∈ {1 ...k − 1}, and
    * The state of C k is q a
* A language is Turing recognisable (recursively enumerable) iff A = L(M) form some Turing Machine M
* A language is Turing decidable iff some Turing machine decides it (recognised by a Turing machine that halts on all input)

## Decidable Languages
* A detemrministic Turing machine can simulate a nondeterministic Turing machine
* L is a Turing recognisable iff some enumerator enumerates L
    * Given enumerators E for language L, enumerate the language and accept is it matches a input w
    * Given Turing machine M for language L, enumerate all strings
* Decidable problems
    * A(DFA) = {<D, w> | D is a DFA that accepts w}
    * A(NFA) = {<N, w> | N is a NFA that accepts w}
    * E(DFA) = {<D> | D is a DFA and L(D) = ∅}
    * EQ(DFA) = {<A, B> | A and B are DFAs and L(A) = L(B)}
    * A(CFG) = {<G, w> | G is a CFG that generates w}
    * E(CFG) = {<G> | G is CFG and L(G)=∅}
    * Every CFL
* **Hierarchy** of Language Classes
    * Regular
    * Context-free
    * Decidable
    * Turing recognisable

## Undecidable Language
* **A(TM)** = {<M, w> | M is a TM and M accepts w}
* **Cantor's Criterion**
    * `card(X) <= card(Y)` iff there is a **total, injective** `f: X -> Y`
    * `card(X) = card(Y)` iff `card(X) <= card(Y)` and `card(Y) <= card(X)`
* Countability
    * X is countable iff card(X) <= card(N)
    * X is countably infinite iff card(x) = card(N)

## Reducibility
* **Halt(TM)** = {<M,w> | M is a Turing machine and M halts when run on input w}
* The set of **Turing recognisable** languaes **closed** under **regular operations**, **NOT closed** under **complement**
* The set of **Dedicable languages** is **closed** under same operations, and ALSO under **complement**
* A language L is **decidable** iff both `L` and its `complement Lc` are **Turing recognisable**
* **E(TM)**, which **A(TM)** is reducible to
* **EQ(TM)** = {<M1, M2> | M1, M2 are TMs and L(M1) = L(M2)}, which E(TM) is redicible to
* **ALL(CFG)** = {< G > | G is a CFG and L(G) = Σ*) is undecidable
* **EQ(CFG)** = {<G, G'> | G, G' are CFGs and L(G) = L(G')}
* Language of invalid computations is context-free
