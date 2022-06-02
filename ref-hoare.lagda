\ifThesis
\chapter{A Hoare-Logic Style Refinement Types Formalisation} \label{ch:wp}
\fi

%\AgdaNoSpaceAroundCode{}
\begin{code}[hide]
open import Agda.Builtin.Nat using (_-_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Primitive
open import Axiom.Extensionality.Propositional
open import Data.Bool hiding (_≤_; _<_)
open import Data.Empty
open import Data.Irrelevant as Irrelevant using (Irrelevant)
open import Data.Nat hiding (_⊔_; _<′_)
-- open import Data.Nat.Base hiding (_⊔_; _<′_)
open import Data.Nat.Properties
open import Data.Product using (Σ; proj₁; proj₂; _,_; <_,_>; uncurry; curry; _×_; ∃; ∃-syntax; ∄; ∄-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (_∘_; _$_; case_of_; id; flip; _ˢ_)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary hiding (Irrelevant)
open import Relation.Unary using (_∩_)
open ≡-Reasoning

-- Only used to mark false theorems.
postulate absurd : ∀{ℓ}{X : Set ℓ} → X
{-# WARNING_ON_USAGE absurd "You have possibly assumed ⊥" #-}

\end{code}

\section{Introduction} \label{sec:ref-agda-intro}

Program verification has been widely adopted by software developers in the past
few decades, and is becoming standard practice when it comes to the development
of safety-critical software. 
Refinement types\footnote{The term \emph{refinement types} is unfortunately quite
overloaded. In this paper, we discuss refinement types in the sense of
\emph{subset types}~\citep{ref-types-name}.}, due to its tight integration into the programming language,
has seen the growing popularity among language designers and users.
It is effective yet easy to harness by
programmers who are less exposed to more sophisticated forms of
formal verification. 
Programmers can annotate their code with types that include
predicates which further restrict the inhabitants of that type. For instance, $\RefTy{ν}{ℕ}{ν > 0}$
is a type that only includes positive natural numbers. We typically call the type being refined, namely $ℕ$ here,
the \emph{base type}, and the logical formula the \emph{refinement predicate}.

Refinement types introduce several complications. Typically, a refinement type system supports
\emph{dependent functions},
which are similar to those in a dependent type system~\citep{Martin-Lof_84}. A dependent function
allows the refinement predicate of the return type to refer to the value of the function's arguments.
Such term-dependency also results in the typing contexts being telescopic, meaning that a type in
the context can refer to variables in earlier entries of that context.

Another source of complexity 
in refinement type systems is solving the logical entailment which determines the subtyping relation
between two types. Usually, some syntactic or semantic rewriting tactics will be employed
to carefully transform the entailment into a certain form, that facilitates the
automatic discharge of
proof obligations using an Satisfiability Modulo Theories (SMT) solver. To ensure that SMT-solving is decidable, language designers typically need to restrict
the logic used for expressing refinement predicates. For instance, in Liquid Haskell~\citep{Vazou_SJ_14}, the quantifier-free
logic of equality, uninterpreted functions and linear arithmetic (QF-EUFLIA) is chosen to ensure decidability.

In the rich literature on refinement types, while there are notable exceptions (e.g.\ \citep{Lehmann_Tanter_16}), due to the complexity of refinement type systems,  
the development remains largely informal%
\footnote{Informal in the sense that they are lacking machine-checked proofs.} and rather ad hoc.
For instance, the typing rules of each variant of a refinement type system can be subtly different,
whereas the underlying reasons for the difference are not always systematically analysed and clearly
attributed. 

The connections between refinement types and Hoare logic have
long been recognised.
For example, the work by \citet{Jhala_Vazou_21} indicates that ``refinement types
can be viewed as a generalization of Floyd-Hoare style program logics.''
The monolithic assertions on the whole program states in Hoare logic
can be decomposed into more fine-grained refinements on
the values of individual terms. Pre- and post-conditions correspond
directly to functions' input and output types.

In a blog post~\citep{Jhala:ref-hl}, Jhala further explains why refinement
types are different (and in some aspects, superior to) Hoare logic, with the punchline that ``types decompose
quantified assertions into quantifier-free refinements", which is a recipe
for rendering the logics decidable for SMT-solvers.

The formal connections between refinement types and Hoare logic deserve more systematic studies.
In this paper, we present a unifying paradigm---a
Hoare logic style formalisation of a refinement
type system on a simply-typed λ-calculus with primitive types,
products and restricted to first-order functions.
Formalising refinement types in the Hoare logic style not only allows us to study
the connections between these two systems, it also makes the formalisation easier
by avoiding the aforementioned complications in refinement type systems.
The formalisation is done in Agda~\citep{Norell:phd, Norell_09}, a
dependently-typed proof assistant. In our formalisation, shallow
Agda terms are used to denote the semantics of the object language and Agda's type system is used as the underlying logic
for the refinement predicates.

In a nutshell, we formulate the typing judgement of the refinement type system
as $Γ ❴ ϕ ❵⊢ e : T ❴ λν.\, ψ ❵$.  When reading it as a regular typing rule,
the typing context is split into two parts: $Γ$ is a list of term variables associated with their base types,
and $ϕ$ contains all the refinement predicates about these variables in the context.
The base type $T$ and the predicate $λν.\, ψ$ form the refinement type
$\RefTy{ν}{T}{ψ}$ that is assigned to $e$.
On the other hand, if we read the rule as a Hoare triple, $e$ is the program and
$ϕ$ and $ψ$ are the pre- and post-conditions of the execution of $e$ under the context $Γ$.

When we make the analogy between refinement type systems and Hoare logic, another analogy naturally arises.
The type analysis with a refinement type system
correlates to the weakest precondition calculation
in Hoare logic. In fact, the idea of using the weakest precondition for refinement type inference is not new.
\citet{Knowles_Flanagan_07} have proposed, as future work, calculating the weakest precondition for refinement type reconstruction.
In this paper, we explore how to use
backward reasoning for typechecking, with our machine-checked formalisation in Agda.

Specifically, this paper presents the following technical contributions:
\begin{itemize}[topsep=1em]
   \item We formalise a refinement type system (\autoref{sec:base-lang} and \autoref{sec:ref-lang})
   \`a la Hoare logic and prove,
  among other meta-theoretical results, that the type system
   is sound and complete with respect to the denotational semantics (\autoref{sec:meta-reflang}).
   \item We define a na\"ive weakest precondition function $\wpc$ in lieu of a typechecking algorithm
   and prove that it is sound and complete with respect to the typing rules
   (\autoref{sec:wp}).
   \item We revise the formalisation above and present a variant of the refinement type system which preserves the
   contracts imposed by functions (i.e.\ λ-abstractions). This requires a more sophisticated
   weakest precondition function $\pre$ and a verification condition generator $\vc$. We again establish the soundness and
   completeness results of $\pre$ and $\vc$ (\autoref{sec:comp-lang}).
\end{itemize}

All the formalisation is developed in and checked by Agda (version 2.6.2.1).
In fact, the main body of this paper is generated from a literate Agda file that contains all
the formal development, including the proofs of all the theorems presented in this paper.
The source file
of this paper can be obtained online (\url{https://github.com/zilinc/ref-hoare}).


\section{The Key Idea}

Typically, a refinement type can be encoded as a Σ-type in a dependently-typed host language.
For example, in Agda's standard library,
a refinement type is defined as a record consisting of a value and an
irrelevant proof of a property $P$ over the value.\footnote{\url{https://github.com/agda/agda-stdlib/blob/367e3d6/src/Data/Refinement.agda}}

\begin{code}[hide]
record Refinement′ {a p} (A : Set a) (P : A → Set p)
                                       : Set (a ⊔ p) where
  constructor _,_
  field value : A
        proof : Irrelevant (P value)
\end{code}

Embedding and working with a dependently-typed language is often quite tedious.
Encoding such an object language in another
dependently-typed language can typically be done with the
help of inductive-recursive techniques~\citep{Dybjer_00}.
The dependent object language features telescopic contexts in the typing rules.
As a result, it poses extra challenges in manipulating typing contexts
and in performing type inference, because the dependency induces
specific topological orders in solving type constraints.

Realising the connections between refinement types and Hoare logic can be a rescue.
When assigning a refinement type to a function (we assume, without loss of generality,
that a function only takes one argument),
the refinement predicate on the argument asserts the properties that the input possesses,
and the predicate on the
result type needs to be satisfied by the output. This mimics the structure of a Hoare
triple: the predicates on the input and on the output correspond to the pre- and post-conditions
respectively.

Another correlation is that, as we have alluded to earlier, in a traditional refinement
typing judgement $\manyv{x_i : τ_i} ⊢ e : τ$ (we use an overhead $\manyv{\text{arrow}}$
to denote an ordered vector, and an overhead $\many{\text{line}}$ for an unordered list;
$τ_i$ and $τ$ here are refinement types),
the refinement predicates in $\many{τ_i}$ correlate to the precondition in a Hoare triple,
and the predicate in $τ$ corresponds to the postcondition.
Concretely, if each $τ_i$ is in the form $\RefTy{ν}{B_i}{ϕ_i}$, we can take the conjunction of all the $ϕ_i$
to form a proposition about $\many{x_i}$, which becomes the precondition describing the program state
(i.e.\ the typing context) under which $e$ is executed.
Similarly, if $τ$ is $\RefTy{ν}{B}{ψ}$, then $ψ$ is the postcondition
that the evaluation result $ν$ of $e$ must satisfy.

The Hoare triple view of refinement types has many advantages.
Firstly, it separates the checking or inference of the
base types and that of the refinement predicates, which is common practice in
languages with refinement types (e.g.\ \citep{Knowles_Flanagan_07, Rondon_KJ_08, Pavlinovic_SW_21}).
The base type information ensures that the refinement predicates are well-typed.
Secondly, the separation of types and predicates means that there is no longer any term-dependency
in types, and there is no telescopic contexts any more. It makes the formalisation and
the reasoning of the system drastically simpler. In particular, the typing contexts no longer
need to maintain any particular order.

In this paper, we study a small simply-typed λ-calculus with primitive types, products, and only first-order
functions.
We assume that all programs are well-typed under the simple type system
and only focus on the type refinement. We require all functions (λ-abstractions) to be annotated with
refinement types and they are the only places where type annotations are needed.
We only typecheck a program against the given annotations,
without elaborating the entire syntax tree with refinement types.
We reduce the typechecking problem to the computation of the weakest precondition of a program
and define a verification condition generator
which aggregates all the proof obligations that need to be fulfilled to witness the
well-typedness of the program. The proof of the verification conditions is
left to the users, who serve as an
oracle for solving all logic puzzles. Therefore we do not concern with the decidability
of the refinement logic.


\section{The Base Language \baselang} \label{sec:base-lang}

Our journey starts with a simply-typed λ-calculus \baselang without any refinement.
The syntax of the \baselang is shown in \autoref{fig:ref-base-syntax}.
It has ground types of unit ($𝟙$), Booleans ($𝟚$) and natural numbers ($ℕ$), and product types.
These types are called base types, meaning that they are the types that can be refined,
i.e.\ they can appear in the base type position $B$ in a typical refinement type $\RefTy{ν}{B}{ϕ}$.
The language is restricted to first-order functions by excluding function
arrows from the first-class base types.
The term language is very standard, consisting of
variables ($x$), constants of the ground types, pairs, projections ($π₁$ and $π₂$),
function applications (denoted by juxtaposition),
if-conditionals, non-recursive local let-bindings, and some arithmetic and logical operators
on natural numbers and Booleans.

Although λ-abstractions can only be directly applied, we do not eschew
them in the syntax. 
This allows us to define top-level functions, which can be reused.
This design decision is primarily only for practical convenience and is otherwise unimportant.
The Agda formalisation follows this design; it handles
function and non-function terms separately. Whenever possible, however,
we merge the two when we present them in this paper.

\begin{figure}
\centering\ssp
\begin{mysyntax}
\text{base types}  & B, S, T & \defd & 𝟙 \mid 𝟚 \mid ℕ \mid S × T & \\
\text{func. types} &   & ∋ & S ⟶ T & \\
\text{expressions} & e & \defd & x \mid () \mid \mathsf{true} \mid \mathsf{false} &  \\
                   &   & \mid  & \mathsf{ze} \mid \mathsf{su}\ e & \\
                   &   & \mid  & (e, e) \mid π₁\ e \mid π₂\ e \mid f\ e & \\
                   &   & \mid  & \If{c}{e₁}{e₂} & \\
                   &   & \mid  & \LET\ x = e₁\ \IN\ e₂ & \\
                   &   & \mid  & e₁ ⊕ e₂ & \\
\text{binary operators} &  & ∋ & ⊕ & \\
\text{functions}   & f & \defd & λx. e & \\
\text{contexts}    & Γ & \defd & \cdot \mid Γ, x : S & 
\end{mysyntax}
\caption{Syntax of the language \baselang}
\label{fig:ref-base-syntax}
\end{figure}

Since the typing rule for \baselang is very standard, we directly show its Agda embedding
and use it as a tutorial on how we construct the language in Agda.
We use an encoding derived from McBride's Kipling language~\citep{McBride_10},
which allows us to index the syntax of the object language with its type in Agda. Therefore,
the object term language is type correct by construction, up to simple types.


\begin{figure}
\begin{tabular}{lr}
{\begin{minipage}{0.18\textwidth}
\begin{code}
data U : Set where
  ‵1′ ‵2′ ‵ℕ′ : U
  _‵×′_   : U → U → U
\end{code}
\begin{code}[hide]
infixl 30 _‵×′_
\end{code}
\end{minipage}} &
{\begin{minipage}{0.3\textwidth}
\begin{code}
⟦_⟧τ : U → Set
⟦ ‵1′ ⟧τ = ⊤
⟦ ‵2′ ⟧τ = Bool
⟦ ‵ℕ′ ⟧τ = ℕ
⟦ S ‵×′ T ⟧τ = ⟦ S ⟧τ × ⟦ T ⟧τ
\end{code}
\end{minipage}}
\end{tabular}
\caption{The Agda definition of the base types and their interpretation}\label{fig:universe}
\end{figure}


In \autoref{fig:universe}, we define a universe $\UNIV$ of codes for base types,
and a decoding function $\denotTy{\cdot}$
(\AgdaOperator{\AgdaFunction{⟦\AgdaUnderscore{}⟧τ}}{} in Agda)
which maps the syntax to the corresponding Agda types.
We do not include a code constructor for function types; a (non-dependent) function type is interpreted
according to its input and output types.

\citet{McBride_10} uses inductive-recursive definitions~\citep{Dybjer_00} for embedding
his dependently-typed object language in Agda, which
is a pretty standard technique (e.g.\ \citep{Danielsson_06, Chapman_09}).
In our base language (and also later with refinement types), since the
term-dependency in types has been eliminated by the Hoare logic style formulation,
the inductive-recursive definition
of the universe \`a la Tarski and its interpretation is not
needed. Nevertheless, we choose to use the vocabulary from that lines of work
since the formalisation is heavily inspired by them.

\begin{figure}
\begin{tabular}{lr}
\begin{minipage}{0.4\columnwidth}
\begin{code}
data Cx : Set where
  ‵Ε′ : Cx
  _▸_ : Cx → U → Cx
\end{code}
\begin{code}[hide]
infixl 24 _▸_
\end{code}
\end{minipage} &
\begin{minipage}{0.6\columnwidth}
\begin{code}
⟦_⟧C : Cx → Set
⟦ ‵Ε′ ⟧C = ⊤
⟦ Γ ▸ S ⟧C = ⟦ Γ ⟧C × ⟦ S ⟧τ
\end{code}
\end{minipage}
\end{tabular}
\caption{The syntax and the denotation of the typing context}
\label{fig:ctx}
\end{figure}


With the denotation of types,
we define what it means for a denotational value to possess a type,
following the work on semantic typing~\citep{Milner_78}.
A denotational value $v$ possesses a type $T$, written $\vDash v : T$, if
$v$ is a member of the semantic domain corresponding to the type $T$.
This is to say, $v$ is a shallow Agda value of type $\denotTy{T}$.

Next, we define the typing context for the language \baselang,
and the denotation of the context in terms of a nested tuple of shallow Agda values (see \autoref{fig:ctx}).
The denotation of the typing context gives us a \emph{semantic
environment} $γ$, mapping variables to their denotational values in Agda.
A semantic environment $γ$ \emph{respects} the typing
context $Γ$ if for all $x ∈ \textsf{dom}(Γ)$,
$\vDash γ(x) : Γ(x)$.

\begin{figure}
{\centering
\begin{code}
data _∋_ : (Γ : Cx)(T : U) → Set where
  top  : ∀{Γ}{T}           → Γ ▸ T ∋ T
  pop  : ∀{Γ}{S T} → Γ ∋ T → Γ ▸ S ∋ T

⟦_⟧∋ : ∀{Γ}{T} → Γ ∋ T → (γ : ⟦ Γ ⟧C) → ⟦ T ⟧τ
⟦ top ⟧∋   (_ , t) = t
⟦ pop i ⟧∋ (γ , _) = ⟦ i ⟧∋ γ
\end{code}}
\caption{Variable indexing in contexts $Γ$ and $γ$}
\label{fig:var-lookup}
\end{figure}

Variables in \baselang are nameless and are referenced by their de Bruijn indices in
the context, with the rightmost (also outermost) element
bound most closely.
Unlike in Kipling~\citep{McBride_10}, the direction to which the context grows
is largely irrelevant, since the context is not telescopic. 
The variable indexing for the typing context $Γ$ and the semantic context $γ$
are defined in \autoref{fig:var-lookup} respectively.

Before we continue,
we introduce a few combinators that
are helpful in simplifying the presentation.
\AgdaFunction{ᵏ}{} and \AgdaFunction{ˢ}{}
are the $\mathbf{K}$ and $\mathbf{S}$ combinators from the SKI calculus. Infix operators
\AgdaFunction{˄}{} and
\AgdaFunction{˅}{} are synonyms to the currying and uncurrying functions respectively.

\begin{code}[hide]
ᵏ : ∀{a b}{Γ : Set a}{X : Set b} → X → Γ → X
{- Function.Base
_ˢ_ : ∀{a b c}
       {Γ : Set a}
       {S : Γ → Set b}
       {T : (γ : Γ) → S γ → Set c}
    → (f : (γ : Γ) → (s : S γ) → T γ s)
    → (s : (γ : Γ) → S γ)
    → (γ : Γ)
    → T γ (s γ)

infixl 20 _ˢ_
-}

ᵏ = Function.const
-- _ˢ_ = λ f s γ → f γ (s γ)

˅ = uncurry  -- ˅ p (s , t) ≡ p s t
˄ = curry    -- ˄ p s t ≡ p (s , t)
\end{code}

The syntax of the language is defined in \autoref{fig:syntax-baselang}, together with
the interpretation functions \AgdaFunction{⟦\_⟧⊢}{} and \AgdaFunction{⟦\_⟧⊢⃗}.
The deep syntax of the object language is indexed by the typing context and
the deep type. It therefore guarantees that the deep terms are type correct by construction.
There is little surprise in the definition of the typing rules.
We only mention that
\AgdaInductiveConstructor{FUN}{} has the same type as a
normal first-class λ-abstraction does. It can be
constructed under any context $Γ$ and does not need to be closed.
A function application can be represented equivalently as a let-binding up to simple types,
but they have different refinement typing rules, as we will see later in this paper.

The interpretation of the term langauge is entirely standard, mapping
object language terms to values of
their corresponding Agda types. On paper, we write $\denotTm{\cdot}$ for the denotation
function, which takes a deep term and a semantic environment and returns
the Agda denotation.



\begin{code}[hide]
infix 10 _⊢_

data ⊕ : Set where
  [+] [-] [<] [≡] [∧] : ⊕

→⊕ : ⊕ → U
→⊕ [+] = ‵ℕ′
→⊕ [-] = ‵ℕ′
→⊕ [<] = ‵ℕ′
→⊕ [≡] = ‵ℕ′
→⊕ [∧] = ‵2′

⊕→ : ⊕ → U
⊕→ [+] = ‵ℕ′
⊕→ [-] = ‵ℕ′
⊕→ [<] = ‵2′
⊕→ [≡] = ‵2′
⊕→ [∧] = ‵2′
\end{code}

\newcommand{\synBL}{%
\begin{code}
data _⊢_ (Γ : Cx) : U → Set
data _⊢_⟶_ (Γ : Cx) : U → U → Set

data _⊢_ Γ where
  VAR   : ∀{T} → Γ ∋ T → Γ ⊢ T
  UNIT  : Γ ⊢ ‵1′
  TT    : Γ ⊢ ‵2′
  FF    : Γ ⊢ ‵2′
  ZE    : Γ ⊢ ‵ℕ′
  SU    : Γ ⊢ ‵ℕ′ → Γ ⊢ ‵ℕ′
  IF    : ∀{T} → Γ ⊢ ‵2′ → Γ ⊢ T → Γ ⊢ T → Γ ⊢ T
  LET   : ∀{S T} → Γ ⊢ S → Γ ▸ S ⊢ T → Γ ⊢ T
  PRD   : ∀{S T} → Γ ⊢ S → Γ ⊢ T → Γ ⊢ (S ‵×′ T)
  FST   : ∀{S T} → Γ ⊢ S ‵×′ T → Γ ⊢ S
  SND   : ∀{S T} → Γ ⊢ S ‵×′ T → Γ ⊢ T
  APP   : ∀{S T} → (Γ ⊢ S ⟶ T) → Γ ⊢ S → Γ ⊢ T
  BOP   : (o : ⊕) → Γ ⊢ →⊕ o → Γ ⊢ →⊕ o → Γ ⊢ ⊕→ o

data _⊢_⟶_ Γ where
  FUN : ∀{S T} → Γ ▸ S ⊢ T → Γ ⊢ S ⟶ T
\end{code}}

\begin{code}[hide]
⟦⟧⊢⊕ : (o : ⊕) → ⟦ →⊕ o ⟧τ → ⟦ →⊕ o ⟧τ → ⟦ ⊕→ o ⟧τ
⟦⟧⊢⊕ [+] = _+_
⟦⟧⊢⊕ [-] = _-_
⟦⟧⊢⊕ [<] = _<ᵇ_
⟦⟧⊢⊕ [≡] = _≡ᵇ_
⟦⟧⊢⊕ [∧] = _∧_

syntax ⟦⟧⊢⊕ o e₁ e₂ = e₁ ⟦ o ⟧⊢⊕ e₂
\end{code}

\newcommand{\denotBL}{%
\begin{code}
⟦_⟧⊢ : ∀{Γ}{T} → Γ ⊢ T → ⟦ Γ ⟧C → ⟦ T ⟧τ
⟦_⟧⊢⃗ : ∀{Γ}{S T} → Γ ⊢ S ⟶ T → ⟦ Γ ⟧C → ⟦ S ⟧τ → ⟦ T ⟧τ

-- 
⟦ VAR x ⟧⊢ = ⟦ x ⟧∋
⟦ UNIT ⟧⊢ = ᵏ tt
⟦ TT ⟧⊢ = ᵏ true
⟦ FF ⟧⊢ = ᵏ false
⟦ ZE ⟧⊢ = ᵏ 0
⟦ SU e ⟧⊢ = ᵏ suc ˢ ⟦ e ⟧⊢
⟦ IF c e₁ e₂ ⟧⊢ = (if_then_else_ ∘ ⟦ c ⟧⊢) ˢ ⟦ e₁ ⟧⊢ ˢ ⟦ e₂ ⟧⊢
⟦ LET e₁ e₂ ⟧⊢ = ˄ ⟦ e₂ ⟧⊢ ˢ ⟦ e₁ ⟧⊢
⟦ PRD e₁ e₂ ⟧⊢ = < ⟦ e₁ ⟧⊢ , ⟦ e₂ ⟧⊢ >
⟦ FST e ⟧⊢ = proj₁ ∘ ⟦ e ⟧⊢
⟦ SND e ⟧⊢ = proj₂ ∘ ⟦ e ⟧⊢
⟦ APP f e ⟧⊢ = ⟦ f ⟧⊢⃗ ˢ ⟦ e ⟧⊢
⟦ BOP o e₁ e₂ ⟧⊢ γ = ⟦ e₁ ⟧⊢ γ ⟦ o ⟧⊢⊕ ⟦ e₂ ⟧⊢ γ

-- 
⟦ FUN e ⟧⊢⃗ = ˄ ⟦ e ⟧⊢
\end{code}}


\begin{figure*}
\begin{tabular}{lr}
\begin{minipage}{0.48\textwidth}{\synBL}\end{minipage} &
\begin{minipage}{0.50\textwidth}{\denotBL}\end{minipage}
\end{tabular}
\caption{The Agda embedding of \baselang and the interpretation, side-by-side.
\AgdaDatatype{⊕}{} is the deep syntax for binary operators; \AgdaFunction{→⊕}{}
and \AgdaFunction{⊕→}{} return the input and output types
of a binary operator respectively.
\AgdaFunction{\AgdaUnderscore{}\AgdaFunction{⟦}\AgdaSpace{}\AgdaBound{o}%
\AgdaSpace{}\AgdaFunction{⟧⊢⊕}\AgdaUnderscore{}}{}
interprets the deep operator \AgdaBound{o} as its Agda counterpart.}
\label{fig:syntax-baselang}
\end{figure*}

As a simple example, if we want to define a top-level function
{\csp
\begin{align*}
f₀ & : ℕ ⟶ ℕ \\
f₀ & = λ x.\, x + 1
\end{align*}}
\begin{code}[hide]
ONE TWO THREE FOUR FIVE SIX SEVEN EIGHT : ∀{Γ} → Γ ⊢ ‵ℕ′
ONE   = SU ZE
TWO   = SU ONE
THREE = SU TWO
FOUR  = SU THREE
FIVE  = SU FOUR
SIX   = SU FIVE
SEVEN = SU SIX
EIGHT = SU SEVEN

suc≡+1 : ∀{x} → suc x ≡ x + 1
suc≡+1 {zero} = refl
suc≡+1 {suc x} = cong suc suc≡+1
\end{code}
%
it can be done in Agda as
%
\begin{center}
\begin{code}
f₀ : ∀{Γ} → Γ ⊢ ‵ℕ′ ⟶ ‵ℕ′
f₀ = FUN (BOP [+] (VAR top) ONE)
\end{code}
\end{center}
where \AgdaFunction{ONE}{} is defined as \AgdaInductiveConstructor{SU}\ \AgdaInductiveConstructor{ZE}.
Note that the function is defined under any context $Γ$.
The denotation of the \AgdaFunction{f₀}{} function under any valid semantic environment $γ$ is:
\begin{center}
\begin{code}
⟦f₀⟧⊢ : ∀{Γ}{γ : ⟦ Γ ⟧C} → ℕ → ℕ
⟦f₀⟧⊢ {γ = γ} = ⟦ f₀ ⟧⊢⃗ γ
\end{code}
\end{center}
Evaluating this term in Agda results in a λ-term: \AgdaSymbol{λ}{} \AgdaBound{x}{} \AgdaSymbol{→}{}
\AgdaBound{x}\AgdaSpace{}%
\AgdaOperator{\AgdaPrimitive{+}}\AgdaSpace{}%
\AgdaNumber{1}, independent of the environment $γ$.

\begin{code}[hide]
sem-typing : ∀{Γ}{T} → (e : Γ ⊢ T) → (γ : ⟦ Γ ⟧C) → ⟦ T ⟧τ
sem-typing e γ = ⟦ e ⟧⊢ γ
\end{code}


\section{Refinement Typed Language \reflang} \label{sec:ref-lang}

We introduce a refinement typed language \reflang that is obtained by equipping \baselang with
refinement predicates. We first present the syntax of the language
in \autoref{fig:ref-ref-syntax}.\footnote{A remark on
the notation: when we talk about the
dependent function types in the object languages, we use a slightly longer function arrow $⟶$ as a reminder that
it is not a first-class type constructor. The typesetting is only subtly different from the normal
function arrow $→$ and in fact its semantics overlaps with that of the normal function arrow. In reading
and understanding the rules, their difference can usually be dismissed.}
The upcast operator for non-function expressions is used to make any refinement subtyping explicit
in the typing tree.

In contrast to the traditional formulation of refinement type systems, where a typing context is defined
as $\manyv{x_i : \tau_i}$, we split it into a base typing context $Γ$ and
a refinement predicate $ϕ$ that can be constructed by taking the conjunction of all predicates in $\many{\tau_i}$.
This formulation is arguably more flexible to work with. It does not enforce any ordering in the context entries,
and it is easier to add path sensitive constraints that are not bound to a program variable.
For example, when typechecking an expression $\If{c}{e₁}{e₂}$, we need to add the constraint $c$ to the context
when we zoom in on $e₁$. This can typically be done by introducing
a fresh (ghost) variable $x$ of an arbitrary base type,
such as $x : \RefTy{ν}{𝟙}{c}$, where $ν ∉ \mathsf{FV}(c)$, and add it to the typing context. In our system,
additional conjuncts can be added to the predicate $ϕ$ directly.

\begin{figure}
\centering \ssp
\begin{mysyntax}
  \text{ref. types}    & τ & \defd & \RefTy{ν}{B}{ϕ}  & \\
  \text{func. types}   &   & ∋ & \RefFunTy{x}{τ}{τ} & \text{(dep. functions)} \\ 
  \text{expressions}   & \hat{e} & \defd & … & \text{(same as \baselang)} \\
                       &   & \mid  & \hat{e} ∷ τ & \text{(upcast)} \\
  \text{functions}  &  \hat{f} & \defd & λ x. \hat{e}  &  \\    
  \text{ref. contexts} & \hat{Γ} & \defd & Γ ; ϕ  & \\
  \text{predicates}    & ϕ, ξ, ψ & \defd & … & \text{(a logic of choice)}
\end{mysyntax}
\caption{Syntax for the language \reflang} \label{fig:ref-ref-syntax}
\end{figure}

Refinement predicates are shallowly embedded as Agda terms of type \AgdaPrimitive{Set}.
We also define a substitution function in Agda
which allows us to substitute the top-most variable in a predicate $ϕ$ with an expression $e$:
\begin{center}
\begin{code}
_[_]s : ∀{Γ}{T} → (ϕ : ⟦ Γ ▸ T ⟧C → Set) → (e : Γ ⊢ T)
      → (⟦ Γ ⟧C → Set)
ϕ [ e ]s = ˄ ϕ ˢ ⟦ e ⟧⊢
\end{code}
\end{center}

\begin{code}[hide]
module Refinement where
\end{code}


\begin{figure}
\centering \csp
\begin{inductive}{\wf{\hat{Γ}}}
\inferrule
  {\textsf{FV}(ϕ) ⊆ \textsf{dom}(Γ)}
  {\wf{Γ;ϕ}}
  {\textsf{Ctx-Wf}}
\end{inductive}
\\
\begin{inductive}{\wf{Γ ⊢ \RefTy{ν}{B}{ψ}}}
\inferrule
  {\textsf{FV}(ψ) ⊆ \textsf{dom}(Γ) ∪ \{ ν \}}
  {\wf{Γ ⊢ \RefTy{ν}{B}{ψ}}}
  {\textsf{RefType-Wf}}
\end{inductive}
\caption{Well-formedness rules for contexts and types}
\label{fig:ref-ref-wf}
\end{figure}



In \autoref{fig:ref-ref-wf}, we show the well-formedness rules for the refinement contexts
and for the refinement types. They are checked by Agda's type system and are therefore implicit
in the Agda formalisation.
The typing rules can be found in \autoref{fig:ref-typing}.
Most of the typing rules are straightforward and work in a similar manner to their counterparts
in a more traditional formalisation of refinement types. We only elaborate on a few of them.


\begin{figure}
\centering \csp
\begin{inductive}{\hat{Γ} ⊢_R \hat{e} : τ}
\inferrule
  {(x : T) ∈ Γ}
  {Γ; ϕ ⊢_R x : \RefTy{ν}{T}{ν = x}}
  {\textsf{VARᴿ}}
\\
\inferrule
  { }
  {\hat{Γ} ⊢_R () : \RefTy{ν}{𝟙}{ν = ()} }
  {\textsf{UNITᴿ}}
\\
\inferrule
  {b ∈ \{ \textsf{true}, \textsf{false} \} }
  {\hat{Γ} ⊢_R b : \RefTy{ν}{𝟚}{ν = b}}
  {\textsf{TTᴿ}/\textsf{FFᴿ}}
\\
\inferrule
  { }
  {\hat{Γ} ⊢_R \ZERO : \RefTy{ν}{ℕ}{ν = 0}}
  {\textsf{ZEᴿ}}
\\
\inferrule
  {\hat{Γ} ⊢_R \hat{e} : \RefTy{ν}{ℕ}{ψ}}
  {\hat{Γ} ⊢_R \SUCC\ \hat{e} : \RefTy{ν}{ℕ}{ν = \textrm{suc}(\hat{e})}}
  {\textsf{SUᴿ}}
\\
\inferrule
  {Γ;ϕ ⊢_R \hat{c} : \RefTy{ν}{𝟚}{ψ'} \\\\
   Γ; ϕ ∧ \hat{c} ⊢_R \hat{e}₁ : \RefTy{ν}{T}{ψ} \\
   Γ; ϕ ∧ ¬\hat{c} ⊢_R \hat{e}₂ : \RefTy{ν}{T}{ψ}}
  {Γ; ϕ ⊢_R \If{\hat{c}}{\hat{e}₁}{\hat{e}₂} : \RefTy{ν}{T}{ψ}}
  {\textsf{IFᴿ}}
\\
\inferrule
  {Γ; ϕ ⊢_R \hat{e}₁ : \RefTy{x}{S}{ξ} \\
   \wf{Γ ⊢ \RefTy{ν}{T}{ψ}} \\\\
   Γ, x:S; ϕ ∧ ξ ⊢_R \hat{e}₂ : \RefTy{ν}{T}{ψ}}
  {Γ; ϕ ⊢_R \LET\ x = \hat{e}₁\ \IN\ \hat{e}₂ : \RefTy{ν}{T}{ψ}}
  {\textsf{LETᴿ}}
\\
\inferrule
  {\hat{Γ} ⊢_R \hat{e}₁ : \RefTy{ν}{S}{ψ₁} \\
   \hat{Γ} ⊢_R \hat{e}₂ : \RefTy{ν}{T}{ψ₂}}
  {\hat{Γ} ⊢_R (\hat{e}₁, \hat{e}₂) : \RefTy{ν}{S × T}{ν = (\hat{e}₁ , \hat{e}₂)}}
  {\textsf{PRDᴿ}}
\\
\inferrule
  {\hat{Γ} ⊢_R \hat{e} : \RefTy{ν}{T₁ × T₂}{ψ} \\
   i ∈ \{1, 2\}}
  {\hat{Γ} ⊢_R πᵢ\ \hat{e} : \RefTy{ν}{Tᵢ}{ν = πᵢ\ \hat{e}}}
  {\textsf{FSTᴿ}/\textsf{SNDᴿ}}
\\
\inferrule
  {Γ; ϕ ⊢_R \hat{f} : \RefFunTy{x}{\RefTy{ν}{S}{ξ}}{\RefTy{ν}{T}{ψ}} \\\\
   x ∉ \textsf{Dom}(Γ) \\
   Γ; ϕ ⊢_R \hat{e} : \RefTy{ν}{S}{ξ}}
  {Γ; ϕ ⊢_R \hat{f}\ \hat{e} : \RefTy{ν}{T}{ψ[\hat{e}/x]}}
  {\textsf{APPᴿ}}
\\
\inferrule
  {\textsf{ty}(⊕) = B₁ → B₁ → B₂ \\\\
   \hat{Γ} ⊢_R \hat{e}₁ : \RefTy{ν}{B₁}{ψ₁} \\
   \hat{Γ} ⊢_R \hat{e}₂ : \RefTy{ν}{B₁}{ψ₂} }
  {\hat{Γ} ⊢_R \hat{e}₁ ⊕ \hat{e}₂ : \RefTy{ν}{B₂}{ν = \hat{e}₁ ⊕ \hat{e}₂}}
  {\textsf{BOPᴿ}}
\\
\inferrule
  {Γ; ϕ ⊢_R \hat{e} : \RefTy{ν}{S}{ψ} \\
   Γ, x : S; ϕ \vDash ψ ⇒ ψ'}
  {Γ; ϕ ⊢_R \hat{e} ∷ \RefTy{ν}{S}{ψ'}}
  {\textsf{SUBᴿ}}
\\
\inferrule
  {Γ; ϕ ⊢_R \hat{e} : \RefTy{ν}{S}{ψ} \\
   Γ \vDash ϕ' ⇒ ϕ }
  {Γ; ϕ' ⊢_R \hat{e} : \RefTy{ν}{S}{ψ}}
  {\textsf{WEAKᴿ}}
\end{inductive}
\\[1em]
\begin{inductive}{\hat{Γ} ⊢_R \hat{f} : \RefFunTy{x}{τ₁}{τ₂}}
\inferrule
  {Γ, x:S; ξ ⊢_R \hat{e} : \RefTy{ν}{T}{ψ}}
  {Γ ; ϕ ⊢_R λ x. e : \RefFunTy{x}{\RefTy{ν}{S}{ξ}}{\RefTy{ν}{T}{ψ}}}
  {\textsf{FUNᴿ}}
\end{inductive}
\caption{Static semantics of \reflang}\label{fig:ref-typing}
\end{figure}


\paragraph{Variables}
The \textsf{VARᴿ} rule infers the most precise type---the singleton type---for a variable $x$.
In many other calculi (e.g.\ \citep{Ou_TMW_04, Knowles_Flanagan_09, Jhala_Vazou_21}),
a different variant of the selfification rule is used for variables:\footnote{We use the subscript in $Γ_{\tau}$ to mean
the more traditional $\manyv{x_i : τ_i}$ context, where each $τ_i$ is a refinement type.}
$$
\centering \csp
\inferrule
  {(x : \RefTy{ν}{B}{ϕ}) ∈ Γ_{\tau}}
  {Γ_{\tau} ⊢ x : \RefTy{ν}{B}{ϕ ∧ ν ≡ x}}
  {\textsf{Self}}
$$
We choose not to include the $ϕ$ in the inferred type of $x$, as such information can be recovered
from the typing context via the subtyping rule \textsf{SUBᴿ}.

\paragraph{Constants}
For value constants ($()$, $\TT$, $\FF$, $\ZERO$) and function constants
($⊕$, $(,)$, $π₁$, $π₂$, $\SUCC$), the typing rules always infer the exact type for the result. 
As with the \textsf{VARᴿ} rule, we do not carry over the refinement predicates in the premises to the
inferred type in the conclusion. Again, no information is lost during this process, as they can be
recovered later from the context when needed.

\paragraph{Function applications}
The typing rule for function applications is pretty standard. In the work of
\citet{Knowles_Flanagan_09}, a compositional version of this rule is used instead.
To summarise the idea, consider the typical function application rule, which has the following form:
\begin{gather*}
\centering \csp
\inferrule
  {Γ_{\tau} ⊢ f : \DepFunTy{x}{τ₁}{τ₂} \\
   Γ_{\tau} ⊢ e : τ₁′ \\ \Subtyping{Γ_{\tau}}{τ₁′}{τ₁} }
  {Γ_{\tau} ⊢ f\ e : τ₂[e/x]}
  {\textsf{App}}
\end{gather*}
In the refinement in the conclusion, the term $e$ is substituted for $x$. This would circumvent
the type abstraction
$τ₁′$ of $e$, exposing the implementation details of the argument to the resulting refinement type $\tau_2[e/x]$.
It also renders the type $τ_2[e/x]$ arbitrarily large due to the presence of $e$. To rectify this problem,
\citet{Knowles_Flanagan_09} propose the result type to be existential: $∃ x:τ₁′.\,τ₂$.
Which application rule to include largely depends on the language design.
We use the traditional one here and the compositional one later in this paper
to contrast the two.

\citet{Jhala_Vazou_21} stick to the regular function application rule, but with some extra
restrictions. They require the function argument to be in A-normal form
(ANF)~\citep{Sabry_Felleisen_92}, i.e.\ the argument being a variable instead of an arbitrary expression.
This reduces the load on the SMT-solver and helps them remain decidable in the refinement logic.
We do not need the ANF restriction in our system for decidability, and the argument term will always
be fully reduced in Agda while conducting the meta-theoretical proofs.


\paragraph{Let-bindings}
In the \textsf{LETᴿ} rule, the well-formedness condition $\wf{Γ ⊢ \RefTy{ν}{T}{ψ}}$ implies that
$ψ$ does not mention the locally-bound variable $x$, preventing the local binder from creeping into
the resulting type of the let-expression. The let-binding and the function application rule give
similar power in reasoning, thanks to the \textsf{SUBᴿ} rule. The structure of the proofs
are slightly different though because the \textsf{SUBᴿ} nodes need to be placed at different positions.


\paragraph{Subtyping and weakening}

Key to a refinement type system is the subtyping relation between types.
Typically, the (partly syntactic) subtyping judgement looks like:

\begin{inductive0}
\inferrule
  {Γ_{\tau}, x : B \vDash ϕ ⇒ ϕ'}
  {\Subtyping{Γ_{\tau}}{\RefTy{ν}{B}{ϕ}}{\RefTy{ν}{B}{ϕ'}}}
  {\textsf{Sub}}
\\
\inferrule
  {\Subtyping{Γ_{\tau}}{σ₂}{σ₁} \\
   \Subtyping{Γ_{\tau}, x:σ₂}{τ₁}{τ₂}}
  {\Subtyping{Γ_{\tau}}{x:σ₁ → τ₁}{x:σ₂ → τ₂}}
  {\textsf{Sub-Fun}}
\end{inductive0}

In our language, since we only support first-order functions, the subtyping rule
for functions is not needed. It can be achieved by promoting the argument and
the result of a function application separately. Since function types are excluded from the universe $\UNIV$,
subtyping can be defined on the entire domain of $\UNIV$, and in a fully semantic manner.
We directly define the subtyping-style rules (\textsf{SUBᴿ}, \textsf{WEAKᴿ})
in terms of a logical entailment: $ϕ \vDash ψ ⇒ ψ′ \defeq ∀ γ\ x.\, ϕ\ γ ∧ ψ\ (γ , x) → ψ′\ (γ , x)$.

If we allowed refinement predicates
over function spaces, it would require a full semantic subtyping relation that also works on the function space.
This has been shown to be possible, e.g.\ interpreting the types in a set-theoretic fashion
as in \citet{Castagna_Frisch_05}'s work. It is however far from trivial to encode a set theory that can be
used for the interpretation of functions in Agda's type system (e.g.\ \citep{kono:zf-agda} is an attempt
to define Zermelo–Fraenkel set theory \textsf{\bfseries ZF} in Agda).




\begin{code}[hide]
  _⊨_⇒_ : ∀{Γ : Cx}{T}(ϕ : ⟦ Γ ⟧C → Set) → (⟦ Γ ▸ T ⟧C → Set) → (⟦ Γ ▸ T ⟧C → Set) → Set
  _⊨_⇒_ {Γ = Γ}{T = T} ϕ ψ ψ′ = ∀(γ : ⟦ Γ ⟧C)(x : ⟦ T ⟧τ) → ϕ γ → ψ (γ , x) → ψ′ (γ , x)
\end{code}

The subtyping rule (\textsf{SUBᴿ}) and the weakening rule (\textsf{WEAKᴿ}) roughly correspond to
the left- and right- consequence rules of Hoare logic respectively. All the subtyping in our system
is explicit. For instance, unlike rule \textsf{App} above, in order to apply a function,
we have to explicitly promote the argument with a \textsf{SUBᴿ} node, if its type is not already
matching the argument type expected by the function. As a notational convenience, in the typing rules
we write $\hat{Γ}⊢_R \hat{e} ∷ τ$ to mean $\hat{Γ} ⊢_R \hat{e} ∷ τ : τ$, as the inferred type is always identical
to the one that is promoted to.



Comparing the \textsf{SUBᴿ} rule with the right-consequence rule in Hoare logic, which reads
\begin{gather*}
\centering \csp
 \inferrule
   {\{ P \}\ s\ \{ Q \} \\
    Q → Q′}
   {\{ P \}\ s\ \{ Q′ \}}
   {\textsf{Cons-R}}
\end{gather*}
we can notice that in the \textsf{SUBᴿ} rule, the implication says $ϕ \vDash ψ ⇒ ψ′$.
In \textsf{Cons-R}, in contrast, the precondition $P$ is not
involved in the implication. This is because of the nature of the underlying language.
In an imperative language to which the Hoare logic is applied, $P$ and $Q$ are predicates
over the program states. A variable
assignment statement or reference update operation will change the state. Therefore after the
execution of the statement $s$, the predicate $P$ is no longer true and all the relevant information
are stored in $Q$. In our purely functional language \reflang, $ϕ$ is a predicate over the typing context $Γ$,
and a typing judgement does not invalidate $ϕ$. Moreover, in practice, when assigning
a refinement type to an expression, the refinement predicate typically only concerns the
term being typed, and does not talk about variables in $Γ$ that are not directly relevant.
Therefore it is technically possible
not to require $ϕ$ in the implication, but it renders the system more cumbersome to use.

As for weakening, in contrast to the more canonical structural rule~\citep{Lehmann_Tanter_16}:
$$
\inferrule
{⊢ Γ_{\tau_1},Γ_{\tau_2},Γ_{\tau_3}\\ Γ_{\tau_1},Γ_{\tau_3} ⊢ e : τ}
{Γ_{\tau_1},Γ_{\tau_2},Γ_{\tau_3} ⊢ e : τ}
$$
the \textsf{WEAKᴿ} rule only changes the predicates in the context and does not allow for adding
new binders to the simply-typed context $Γ$.
It compares favourably to those with a more syntactic refinement-typing context.
For a traditional refinement-typing context $\manyv{x_i : \tau_i}$, if the weakening lemma is
to be defined in a general enough manner
to allow weakening to happen arbitrarily in the middle of the context, some tactics will be required
to syntactically rearrange the context to make the weakening rule applicable.
Our weakening rule is purely semantic and therefore does not require syntactic rewriting before
it can be applied.


\paragraph{Functions} The \textsf{FUNᴿ} rule can be used to construct a λ-abstraction
under any context $Γ$ and the λ-term does not need to be closed. The function body $\hat{e}$
is typed under the extended context $Γ,x:S$, but the predicate part does not include $ϕ$.
This does not cause any problems because $ξ$ is itself a predicate over the context and the
function argument, and also if more information about the context needs to be drawn, it can
be done via the \textsf{SUBᴿ} rule at a later stage.

% \begin{center} *\quad*\quad* \end{center}

The pen-and-paper formalisation above leaves some aspects informal for presentation purposes.
One instance of the discrepancy is that, when we type the term $\hat{e}₁ + \hat{e}₂$, the resulting predicate
is $ν = \hat{e}₁ + \hat{e}₂$. What has been implicit in the rules is the reflection of
object terms into the logical system. 


In our formal development, the underlying logical system is Agda's
type system, therefore we want to reflect the refinement-typed term language into the
Agda land. We do it as a two-step process: we first map the refinement-typed language to
the simply-typed language by erasure, and then reflect the simply-typed terms into logic
using the already-defined interpretation function $\denotTm{\cdot}$, with which we interpret
the object language as Agda terms.

The erasure function $⌜\cdot⌝ᴿ$ removes all refinement type information from a refinement-typed term
(also, typing tree) and returns a corresponding simply-typed term (also, typing tree).
Essentially, the erasure function removes the refinement predicates, and any explicit upcast (\textsf{SUBᴿ}) nodes
from the typing tree.


Now we can define the deep syntax of the \reflang language along with its typing rules in Agda.
When an expression $\hat{e}$ in the object language has an Agda type
\AgdaDatatype{%
\AgdaBound{Γ}\AgdaSpace{}%
\AgdaOperator{%
%<*AgdaTag-❴>
\AgdaDatatype{❴}%
%</AgdaTag-❴>
}\AgdaSpace{}%
\AgdaBound{ϕ}\AgdaSpace{}%
\AgdaOperator{%
%<*AgdaTag-❵⊢>
\AgdaDatatype{❵⊢}%
%</AgdaTag-❵⊢>
}\AgdaSpace{}%
\AgdaBound{T}\AgdaSpace{}%
\AgdaOperator{%
%<*AgdaTag-❴>
\AgdaDatatype{❴}%
%</AgdaTag-❴>
}\AgdaSpace{}%
\AgdaBound{ψ}\AgdaSpace{}%
\AgdaOperator{%
%<*AgdaTag-❵>
\AgdaDatatype{❵}%
%</AgdaTag-❵>
}}\AgdaSpace{},
it means that under context $Γ$ which satisfies the precondition $ϕ$, the expression $\hat{e}$
can be assigned a refinement type $\RefTy{ν}{T}{ψ}$. For functions, we have
\AgdaDatatype{%
\AgdaBound{Γ}\AgdaSpace{}%
❴\AgdaSpace{}%
\AgdaBound{ϕ}\AgdaSpace{}❵⊢\AgdaSpace{}%
\AgdaBound{S}\AgdaSpace{}❴\AgdaSpace{}%
\AgdaBound{ξ}\AgdaSpace{}❵⟶\AgdaSpace{}%
\AgdaBound{T}\AgdaSpace{}❴\AgdaSpace{}%
\AgdaBound{ψ}\AgdaSpace{}❵} 
which keeps track
of the predicates on the context $Γ$, on the argument and on the result respectively.
The datatypes and the erasure function $⌜\cdot⌝ᴿ$ are inductive-recursively defined.
For space reasons, we omit the Agda definitions from the paper. They can be found in the
Agda source file of the paper.

The context weakening rule \textsf{WEAKᴿ} in \autoref{fig:ref-typing}
is in fact admissible in our system, therefore it is not included
as a primitive construct in the formal definition of the language.

\begin{lemma}[Weakening is admissible]
For any typing tree $Γ;ϕ ⊢_R \hat{e} : τ$, if $ϕ′ ⇒ ϕ$ under any semantic environment
$γ$ that respects $Γ$,
then there exists a typing tree with the stronger context $Γ ; ϕ′$, such that
$Γ;ϕ′ ⊢_R \hat{e}′ : τ$ and $⌜ \hat{e} ⌝ᴿ = ⌜ \hat{e}′ ⌝ᴿ$.
\end{lemma}

\begin{code}[hide]
  -- Refinement typing with a pre- and a post-condition.
  data _❴_❵⊢_❴_❵ (Γ : Cx) : (⟦ Γ ⟧C → Set)
                          → (T : U)
                          → (⟦ Γ ▸ T ⟧C → Set)
                          → Set₁

  data _❴_❵⊢_❴_❵⟶_❴_❵ (Γ : Cx) : (⟦ Γ ⟧C → Set)
                               → (S : U)
                               → (⟦ Γ ▸ S ⟧C → Set)
                               → (T : U)
                               → (⟦ Γ ▸ S ▸ T ⟧C → Set)
                               → Set₁

  -- Erasure.
  ⌜_⌝ᴿ  : ∀{Γ}{T}{ϕ}{ψ} → Γ ❴ ϕ ❵⊢ T ❴ ψ ❵ → Γ ⊢ T
  ⌜_⌝ᴿ⃗ : ∀{Γ}{S T}{ϕ}{ξ}{ψ} → Γ ❴ ϕ ❵⊢ S ❴ ξ ❵⟶ T ❴ ψ ❵ → Γ ⊢ S ⟶ T

  data _❴_❵⊢_❴_❵ Γ where
    VARᴿ   : ∀{ϕ}{T} → (i : Γ ∋ T) → Γ ❴ ϕ ❵⊢ T ❴ (λ (γ , ν) → ν ≡ ⟦ i ⟧∋ γ) ❵
    UNITᴿ  : ∀{ϕ} → (Γ ❴ ϕ ❵⊢ ‵1′ ❴ (λ γ → proj₂ γ ≡ tt) ❵)
    TTᴿ    : ∀{ϕ} → Γ ❴ ϕ ❵⊢ ‵2′ ❴ (λ γ → proj₂ γ ≡ true ) ❵
    FFᴿ    : ∀{ϕ} → Γ ❴ ϕ ❵⊢ ‵2′ ❴ (λ γ → proj₂ γ ≡ false) ❵
    ZEᴿ    : ∀{ϕ} → Γ ❴ ϕ ❵⊢ ‵ℕ′ ❴ (λ γ → proj₂ γ ≡ 0 ) ❵
    SUᴿ    : ∀{ϕ}{ψ}
           → (n : Γ ❴ ϕ ❵⊢ ‵ℕ′ ❴ ψ ❵)
           → Γ ❴ ϕ ❵⊢ ‵ℕ′ ❴ (λ γ → proj₂ γ ≡ suc (⟦ ⌜ n ⌝ᴿ ⟧⊢ (proj₁ γ))) ❵
    IFᴿ    : ∀{ϕ}{ξ}{T}{ψ}
           → (c : Γ ❴ ϕ ❵⊢ ‵2′ ❴ ξ ❵)
           → (Γ ❴ (λ γ → ϕ γ × ⟦ ⌜ c ⌝ᴿ ⟧⊢ γ ≡ true ) ❵⊢ T ❴ ψ ❵)
           → (Γ ❴ (λ γ → ϕ γ × ⟦ ⌜ c ⌝ᴿ ⟧⊢ γ ≡ false) ❵⊢ T ❴ ψ ❵)
           → Γ ❴ ϕ ❵⊢ T ❴ ψ ❵
    LETᴿ   : ∀{S}{T}{ϕ}{ξ : ⟦ Γ ▸ S ⟧C → Set}{ψ : ⟦ Γ ▸ T ⟧C → Set}
           → (e₁ : Γ ❴ ϕ ❵⊢ S ❴ ξ ❵)
           → (e₂ : (Γ ▸ S) ❴ (λ (γ , s) → ϕ γ × ξ (γ , s)) ❵⊢ T ❴ (λ ((γ , _) , ν) → ψ (γ , ν)) ❵)
           → Γ ❴ ϕ ❵⊢ T ❴ ψ ❵
    PRDᴿ   : ∀{S T}{ϕ}{ψ₁ ψ₂}
           → (e₁ : Γ ❴ ϕ ❵⊢ S ❴ ψ₁ ❵)
           → (e₂ : Γ ❴ ϕ ❵⊢ T ❴ ψ₂ ❵)
           → Γ ❴ ϕ ❵⊢ S ‵×′ T ❴ (λ (γ , ν) → ν ≡ < ⟦ ⌜ e₁ ⌝ᴿ ⟧⊢ , ⟦ ⌜ e₂ ⌝ᴿ ⟧⊢ > γ) ❵
    FSTᴿ   : ∀{S T}{ϕ}{ψ}
           → (e : Γ ❴ ϕ ❵⊢ S ‵×′ T ❴ ψ ❵)
           → Γ ❴ ϕ ❵⊢ S ❴ (λ (γ , ν) → ν ≡ proj₁ (⟦ ⌜ e ⌝ᴿ ⟧⊢ γ)) ❵
    SNDᴿ   : ∀{S T}{ϕ}{ψ}
           → (e : Γ ❴ ϕ ❵⊢ S ‵×′ T ❴ ψ ❵)
           → Γ ❴ ϕ ❵⊢ T ❴ (λ (γ , ν) → ν ≡ proj₂ (⟦ ⌜ e ⌝ᴿ ⟧⊢ γ)) ❵
    APPᴿ   : ∀{S}{T}{ϕ}{ξ}{ψ}
           → (f : Γ ❴ ϕ ❵⊢ S ❴ ξ ❵⟶ T ❴ ψ ❵)
           → (e : Γ ❴ ϕ ❵⊢ S ❴ ξ ❵)
           → Γ ❴ ϕ ❵⊢ T ❴ (λ (γ , t) → ψ ((γ , ⟦ ⌜ e ⌝ᴿ ⟧⊢ γ) , t)) ❵
    BOPᴿ  : ∀{ϕ}(o : ⊕){ψ₁ ψ₂}
           → (e₁ : Γ ❴ ϕ ❵⊢ →⊕ o ❴ ψ₁ ❵)
           → (e₂ : Γ ❴ ϕ ❵⊢ →⊕ o ❴ ψ₂ ❵)
           → Γ ❴ ϕ ❵⊢ ⊕→ o ❴ (λ (γ , ν) → ν ≡ (⟦ ⌜ e₁ ⌝ᴿ ⟧⊢ γ ⟦ o ⟧⊢⊕ ⟦ ⌜ e₂ ⌝ᴿ ⟧⊢ γ)) ❵
    SUBᴿ   : ∀{T}{ϕ : ⟦ Γ ⟧C → Set}{ψ : ⟦ Γ ▸ T ⟧C → Set}
           → (e : Γ ❴ ϕ ❵⊢ T ❴ ψ ❵)
           → (ψ′ : ⟦ Γ ▸ T ⟧C → Set)
           → ϕ ⊨ ψ ⇒ ψ′
           → Γ ❴ ϕ ❵⊢ T ❴ ψ′ ❵

  data _❴_❵⊢_❴_❵⟶_❴_❵ Γ where
    FUNᴿ   : ∀{S T}{ϕ}{ξ}{ψ}
           → Γ ▸ S ❴ ξ ❵⊢ T ❴ ψ ❵
           → Γ ❴ ϕ ❵⊢ S ❴ ξ ❵⟶ T ❴ ψ ❵


  ⌜ VARᴿ i ⌝ᴿ = VAR i
  ⌜ UNITᴿ ⌝ᴿ = UNIT
  ⌜ TTᴿ ⌝ᴿ = TT
  ⌜ FFᴿ ⌝ᴿ = FF
  ⌜ ZEᴿ ⌝ᴿ = ZE
  ⌜ SUᴿ n ⌝ᴿ = SU ⌜ n ⌝ᴿ
  ⌜ IFᴿ c e₁ e₂ ⌝ᴿ = IF ⌜ c ⌝ᴿ ⌜ e₁ ⌝ᴿ ⌜ e₂ ⌝ᴿ
  ⌜ LETᴿ e₁ e₂ ⌝ᴿ = LET ⌜ e₁ ⌝ᴿ ⌜ e₂ ⌝ᴿ
  ⌜ PRDᴿ e₁ e₂ ⌝ᴿ = PRD ⌜ e₁ ⌝ᴿ ⌜ e₂ ⌝ᴿ
  ⌜ FSTᴿ e ⌝ᴿ = FST ⌜ e ⌝ᴿ
  ⌜ SNDᴿ e ⌝ᴿ = SND ⌜ e ⌝ᴿ
  ⌜ APPᴿ f e ⌝ᴿ = APP ⌜ f ⌝ᴿ⃗ ⌜ e ⌝ᴿ
  ⌜ BOPᴿ o e₁ e₂ ⌝ᴿ = BOP o ⌜ e₁ ⌝ᴿ ⌜ e₂ ⌝ᴿ
  ⌜ SUBᴿ e _ _ ⌝ᴿ = ⌜ e ⌝ᴿ

  ⌜ FUNᴿ e ⌝ᴿ⃗ = FUN ⌜ e ⌝ᴿ


  weak-admissible⃗ : ∀{Γ}{S T}{ϕ ϕ′}{ξ}{ψ}
                   → (f : Γ ❴ ϕ ❵⊢ S ❴ ξ ❵⟶ T ❴ ψ ❵)
                   → ((γ : ⟦ Γ ⟧C) → ϕ′ γ → ϕ γ)
                   → Σ (Γ ❴ ϕ′ ❵⊢ S ❴ ξ ❵⟶ T ❴ ψ ❵) λ f′ → ⌜ f ⌝ᴿ⃗ ≡ ⌜ f′ ⌝ᴿ⃗
  weak-admissible⃗ (FUNᴿ e) wk = FUNᴿ e , refl

  weak-admissible : ∀{Γ}{T}{ϕ ϕ′}{ψ}
                  → (e : Γ ❴ ϕ ❵⊢ T ❴ ψ ❵)
                  → ((γ : ⟦ Γ ⟧C) → ϕ′ γ → ϕ γ)
                  → Σ (Γ ❴ ϕ′ ❵⊢ T ❴ ψ ❵) λ e′ → ⌜ e ⌝ᴿ ≡ ⌜ e′ ⌝ᴿ
  weak-admissible (VARᴿ i) wk = (VARᴿ i) , refl
  weak-admissible UNITᴿ wk = UNITᴿ , refl
  weak-admissible TTᴿ wk = TTᴿ , refl
  weak-admissible FFᴿ wk = FFᴿ , refl
  weak-admissible ZEᴿ wk = ZEᴿ , refl
  weak-admissible (SUᴿ e) wk
    with e′ , e-≡ ← weak-admissible e wk
    rewrite e-≡ = SUᴿ e′ , refl
  weak-admissible {ϕ′ = ϕ′} (IFᴿ c e₁ e₂) wk
    with c′ , c-≡ ← weak-admissible c wk |
         e₁′ , e₁-≡ ← weak-admissible {ϕ′ = λ γ → ϕ′ γ × ⟦ ⌜ c ⌝ᴿ ⟧⊢ γ ≡ true } e₁ (λ γ (ϕ′ , c≡tt) → wk γ ϕ′ , c≡tt) |
         e₂′ , e₂-≡ ← weak-admissible {ϕ′ = λ γ → ϕ′ γ × ⟦ ⌜ c ⌝ᴿ ⟧⊢ γ ≡ false} e₂ (λ γ (ϕ′ , c≡ff) → wk γ ϕ′ , c≡ff)
    rewrite c-≡ | e₁-≡ | e₂-≡ = IFᴿ c′ e₁′ e₂′ , refl
  weak-admissible {ϕ′ = ϕ′} (LETᴿ e₁ e₂) wk
    with e₁′ , e₁-≡ ← weak-admissible e₁ wk |
         e₂′ , e₂-≡ ← weak-admissible e₂ (λ (γ , s) (ϕ′-prf , ξ-prf) → wk γ ϕ′-prf , ξ-prf)
    rewrite e₁-≡ | e₂-≡ = LETᴿ e₁′ e₂′ , refl
  weak-admissible (PRDᴿ e₁ e₂) wk
    with e₁′ , e₁-≡ ← weak-admissible e₁ wk |
         e₂′ , e₂-≡ ← weak-admissible e₂ wk
    rewrite e₁-≡ | e₂-≡ = PRDᴿ e₁′ e₂′ , refl
  weak-admissible (FSTᴿ e) wk
    with e′ , e-≡ ← weak-admissible e wk
    rewrite e-≡ = FSTᴿ e′ , refl
  weak-admissible (SNDᴿ e) wk
    with e′ , e-≡ ← weak-admissible e wk
    rewrite e-≡ = SNDᴿ e′ , refl
  weak-admissible (APPᴿ f e) wk
    with f′ , f-≡ ← weak-admissible⃗ f wk |
         e′ , e-≡ ← weak-admissible e wk
    rewrite f-≡ | e-≡ = APPᴿ f′ e′ , refl
  weak-admissible (BOPᴿ o e₁ e₂) wk
    with e₁′ , e₁-≡ ← weak-admissible e₁ wk |
         e₂′ , e₂-≡ ← weak-admissible e₂ wk
    rewrite e₁-≡ | e₂-≡ = BOPᴿ o e₁′ e₂′ , refl
  weak-admissible (SUBᴿ e ψ′ sub) wk
    with e′ , e-≡ ← weak-admissible e wk
    rewrite e-≡ = SUBᴿ e′ ψ′ (λ γ ν ϕ-prf ψ-prf → sub γ ν (wk γ ϕ-prf) ψ-prf) , refl
\end{code}


Continuing on the \AgdaFunction{f₀}{} function defined in \autoref{sec:base-lang},
if we want to lift it to a function
definition in \reflang, we will need to add refinements and insert explicit upcast nodes:
%
{\csp
\begin{align*}
f₀ᴿ & :\MyDepFunTy{x}{\RefTy{ν}{ℕ}{ν < 2}}{\RefTy{ν}{ℕ}{ν < 4}} \\
f₀ᴿ & = λ x.\, (x + 1 ∷ \RefTy{ν}{ℕ}{ν < 4})
\end{align*}}
%
In Agda, it is defined as follows:
\begin{code}[hide]
  ONEᴿ TWOᴿ THREEᴿ : ∀{Γ}{ϕ} → Γ ❴ ϕ ❵⊢ ‵ℕ′ ❴ _ ❵
  ONEᴿ = SUᴿ ZEᴿ
  TWOᴿ = SUᴿ ONEᴿ
  THREEᴿ = SUᴿ TWOᴿ

  s<2⇒t≡s+1⇒s+1<4 : ∀{s t : ℕ} → s < 2 → t ≡ s + 1 → t < 4
  s<2⇒t≡s+1⇒s+1<4 {s} s<2 t≡s+1 rewrite t≡s+1 | sym (suc≡+1 {s}) = s≤s (≤-trans s<2 (s≤s (s≤s z≤n)))
\end{code}

{\centering
\begin{code}
  f₀ᴿ : ‵Ε′ ❴ ᵏ ⊤ ❵⊢ ‵ℕ′ ❴ (_< 2) ∘ proj₂ ❵⟶
                     ‵ℕ′ ❴ (_< 4) ∘ proj₂ ❵
  f₀ᴿ = FUNᴿ (SUBᴿ (BOPᴿ [+] (VARᴿ top) ONEᴿ) _ prf)
\end{code}}

\begin{code}[hide]
    where prf = λ (_ , s) t s<2 t≡s+1 → s<2⇒t≡s+1⇒s+1<4 s<2 t≡s+1
\end{code}

The upcast node \AgdaInductiveConstructor{SUBᴿ}{} needs to be accompanied by an evidence
(i.e.\ an Agda proof term \AgdaFunction{prf}{} whose definition is omitted)
to witness the semantic entailment $x < 2 \vDash ν = x + 1 ⇒ ν < 4$.

To demonstrate the function application of \AgdaFunction{f₀ᴿ}{}, we define the following
expression:
%
\begin{code}[hide]
  ex₀ : ‵Ε′ ⊢ ‵ℕ′
  ex₀ = APP f₀ ONE
\end{code}
%
{\csp
\begin{align*}
ex₀ᴿ & : \RefTy{ν}{ℕ}{ν < 5} \\
ex₀ᴿ & = f₀ᴿ\ (1 ∷ \RefTy{ν}{ℕ}{ν < 2}) ∷ \RefTy{ν}{ℕ}{ν < 5}
\end{align*}}
%
The inner upcast is for promoting the argument $1$, which is inferred the exact type
$\RefTy{ν}{ℕ}{ν = 1}$, to match $f₀ᴿ$'s argument type.
The outer upcast is for promoting the result of the application from $\RefTy{ν}{ℕ}{ν < 4}$
to $\RefTy{ν}{ℕ}{ν < 5}$.
%
In Agda, two proof terms need to be constructed for the upcast nodes
in order to show that the argument and the result of the application are both
type correct:

\begin{code}[hide]
  s≡1⇒s<2 : ∀{s} → s ≡ 1 → s < 2
  s≡1⇒s<2 {s} s≡1 rewrite s≡1 = s≤s (s≤s z≤n)

  t<4⇒t<5 : ∀{t} → t < 4 → t < 5
  t<4⇒t<5 t<4 = <-trans t<4 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
\end{code}

{\centering
\begin{code}
  ex₀ᴿ : ‵Ε′ ❴ ᵏ ⊤ ❵⊢ ‵ℕ′ ❴ (_< 5) ∘ proj₂ ❵
  ex₀ᴿ = SUBᴿ (APPᴿ {ψ = (_< 4) ∘ proj₂} f₀ᴿ
                    (SUBᴿ ONEᴿ _ λ _ _ _ → s≡1⇒s<2))
              _ λ _ _ _ → t<4⇒t<5
\end{code}}


\section{Meta-Properties of \reflang} \label{sec:meta-reflang}


Instead of proving the textbook type soundness theorems (progress and
preservation)~\citep{Wright_Felleisen_94, Harper:pfpl} that
rest upon subject reduction, we instead get for free the semantic type soundness theorem
\`a la Milner~\citep{Milner_78} for the base language \baselang because of the way
the term language is embedded and interpreted in Agda.

\begin{theorem}[Semantic soundness]
If $Γ ⊢ e : T$ and the semantic environment $γ$ respects the typing environment $Γ$,
then $\vDash \denotTm{e} γ : T$.
\end{theorem}

\begin{code}[hide]
  base-type-soundness : ∀{Γ}{T} → (e : Γ ⊢ T) → (γ : ⟦ Γ ⟧C) → ⟦ T ⟧τ
  base-type-soundness e γ = ⟦ e ⟧⊢ γ

  base-type-soundness⃗ : ∀{Γ}{S T} → (e : Γ ⊢ S ⟶ T) → (γ : ⟦ Γ ⟧C) → (⟦ S ⟧τ → ⟦ T ⟧τ)
  base-type-soundness⃗ e γ = ⟦ e ⟧⊢⃗ γ
\end{code}

We take the same semantic approach to type soundness and establish the the refinement soundness
theorem for \reflang. We use the notation $ϕ \vDash ψ$ for the semantic entailment relation in the underlying
logic, which, in our case, is Agda's type system. To relate a semantic environment $γ$ to
a refinement typing context $\hat{Γ}$, we proceed with the following definitions.

\begin{definition}
A semantic environment $γ$ satisfies a predicate $ϕ$, if $\textsf{FV}(ϕ) \subseteq \textsf{dom}(γ)$ and
$\varnothing \vDash ϕ\ γ$. We write $ϕ\ γ$ to mean $ϕ[\many{γ(x_i)/x_i}]$ for all free variables $x_i$ in $ϕ$.
\end{definition}

\begin{definition}
A semantic environment $γ$ respects a refinement typing context $Γ;ϕ$
if $γ$ respects $Γ$ and satisfies $ϕ$.
\end{definition}

We define what it means for a denotational
value to possess a refinement type, and extend the notion of semantic typing to refinement types.

\begin{definition}
A value $v$ posesses a refinement type $\RefTy{ν}{T}{ψ}$, written $\vDash v : \RefTy{ν}{T}{ψ}$,
if $\vDash v : T$ and $\varnothing \vDash ψ[v/ν]$.
\end{definition}

\begin{definition}[Refinement semantic typing]
$\hat{Γ} \vDash \hat{e} : τ$ if $\vDash \denotTm{⌜\hat{e}⌝ᴿ}γ : τ$ for all $γ$ that respects $\hat{Γ}$.
\end{definition}

With the notion of refinement semantic typing, we can state the refinement
(semantic) type soundness theorem as follows.

\begin{theorem}[Refinement soundness]\label{thm:ref-soundness}
If $\hat{Γ} ⊢_R \hat{e} : τ$ then $\hat{Γ} \vDash e : τ$.
\end{theorem}

The converse of this theorem is also true. It states the completeness of our
refinement type system with respect to semantic typing.

\begin{theorem}[Refinement completeness]\label{thm:ref-completeness}
If $Γ ⊢ e : T$ and for all semantic context $γ$
that respects $\hat{Γ}$, $\vDash \denotTm{e}γ : \RefTy{ν}{T}{ψ}$, then
there exists a refinement typing $\hat{Γ} ⊢_R \hat{e} : \RefTy{ν}{T}{ψ}$
such that $⌜ \hat{e} ⌝ᴿ = e$.
\end{theorem}

Note that for the completeness theorem, since we only need to construct
one such refinement typed expression (or equivalently, typing tree), the
proof is not unique, in light of the \textsf{SUBᴿ} and \textsf{WEAKᴿ} rules.


\begin{code}[hide]
  ref-soundness : ∀{Γ}{ϕ}{γ : ⟦ Γ ⟧C}{T}{ψ}
                → (e : Γ ❴ ϕ ❵⊢ T ❴ ψ ❵)
                → (ϕ γ → ψ (γ , ⟦ ⌜ e ⌝ᴿ ⟧⊢ γ))
  ref⃗-soundness : ∀{Γ}{γ : ⟦ Γ ⟧C}{S T}{ϕ}{ξ}{ψ}
                 → (f : Γ ❴ ϕ ❵⊢ S ❴ ξ ❵⟶ T ❴ ψ ❵)
                 → (x : ⟦ S ⟧τ) → ϕ γ → ξ (γ , x) → ψ ((γ , x) , ⟦ ⌜ f ⌝ᴿ⃗ ⟧⊢⃗ γ x)

  ref-soundness (VARᴿ _) _ = refl
  ref-soundness UNITᴿ _ = refl
  ref-soundness TTᴿ _ = refl
  ref-soundness FFᴿ _ = refl
  ref-soundness ZEᴿ _ = refl
  ref-soundness (SUᴿ _) _ = refl
  ref-soundness {γ = γ} (IFᴿ c e₁ e₂) ϕ-prf with ⟦ ⌜ c ⌝ᴿ ⟧⊢ γ in cond
  ... | true  = ref-soundness e₁ (ϕ-prf , cond)
  ... | false = ref-soundness e₂ (ϕ-prf , cond)
  ref-soundness (LETᴿ e₁ e₂) ϕ-prf = ref-soundness e₂ (ϕ-prf , ref-soundness e₁ ϕ-prf)
  ref-soundness (PRDᴿ _ _) _ = refl
  ref-soundness (FSTᴿ _) _ = refl
  ref-soundness (SNDᴿ _) _ = refl
  ref-soundness {γ = γ}(APPᴿ f e) ϕ-prf
    = ref⃗-soundness {γ = γ} f (⟦ ⌜ e ⌝ᴿ ⟧⊢ γ) ϕ-prf (ref-soundness e ϕ-prf)
  ref-soundness (BOPᴿ _ _ _) _ = refl
  ref-soundness {γ = γ} (SUBᴿ e _ sub) ϕ-prf = sub γ (⟦ ⌜ e ⌝ᴿ ⟧⊢ γ) ϕ-prf (ref-soundness e ϕ-prf)

  ref⃗-soundness {γ = γ} (FUNᴿ e) x _  = ref-soundness e

  ref-soundness′ : ∀{T}{ψ}
                 → (e : ‵Ε′ ❴ ᵏ ⊤ ❵⊢ T ❴ ψ ❵)
                 → ψ (tt , ⟦ ⌜ e ⌝ᴿ ⟧⊢ tt)
  ref-soundness′ e = ref-soundness e tt

  ref-completeness : ∀{Γ}{T}{ϕ}{ψ}
                   → (e : Γ ⊢ T)
                   → ((γ : ⟦ Γ ⟧C) → ϕ γ → ψ (γ , ⟦ e ⟧⊢ γ))
                   → Σ (Γ ❴ ϕ ❵⊢ T ❴ ψ ❵) λ e′ → ⌜ e′ ⌝ᴿ ≡ e
  ref⃗-completeness : ∀{Γ}{S T}{ϕ}{ξ}{ψ}
                    → (f : Γ ⊢ S ⟶ T)
                    → (∀(γ : ⟦ Γ ⟧C)(x : ⟦ S ⟧τ) → ξ (γ , x) → ψ ((γ , x) , ⟦ f ⟧⊢⃗ γ x))
                    → Σ (Γ ❴ ϕ ❵⊢ S ❴ ξ ❵⟶ T ❴ ψ ❵) λ f′ → ⌜ f′ ⌝ᴿ⃗ ≡ f

  ref-completeness {ψ = ψ} (VAR x) prf = SUBᴿ (VARᴿ x) ψ (λ γ _ ϕ-prf x-≡ → subst _ (sym x-≡) (prf γ ϕ-prf)) , refl
  ref-completeness {ψ = ψ} UNIT prf = SUBᴿ UNITᴿ ψ (λ γ _ ϕ-prf x-≡ → subst _ (sym x-≡) (prf γ ϕ-prf)) , refl
  ref-completeness {ψ = ψ} TT prf = SUBᴿ TTᴿ ψ (λ γ _ ϕ-prf x-≡ → subst (˄ ψ γ) (sym x-≡) (prf γ ϕ-prf)) , refl
  ref-completeness {ψ = ψ} FF prf = SUBᴿ FFᴿ ψ (λ γ _ ϕ-prf x-≡ → subst (˄ ψ γ) (sym x-≡) (prf γ ϕ-prf)) , refl
  ref-completeness {ψ = ψ} ZE prf = SUBᴿ ZEᴿ ψ (λ γ _ ϕ-prf x-≡ → subst (˄ ψ γ) (sym x-≡) (prf γ ϕ-prf)) , refl
  ref-completeness {ϕ = ϕ}{ψ = ψ} (SU e) prf
    with e′ , e-≡ ← ref-completeness {ψ = ᵏ ⊤} e (λ _ _ → tt)
    rewrite sym e-≡
    = SUBᴿ (SUᴿ e′) ψ (λ γ _ ϕ-prf x-≡ → subst (˄ ψ γ) (sym x-≡) (subst (λ x → ˄ ψ γ (suc (⟦ x ⟧⊢ γ))) (sym e-≡) (prf γ ϕ-prf))) , refl
  ref-completeness {ϕ = ϕ}{ψ = ψ} (IF c e₁ e₂) prf
    with c′ , c-≡ ← ref-completeness {ϕ = ϕ}{ψ = ᵏ ⊤} c (λ _ _ → tt) |
         e₁′ , e₁-≡ ← ref-completeness {ϕ = λ γ → ϕ γ × ⟦ c ⟧⊢ γ ≡ true }{ψ = ψ} e₁ (λ γ ϕ-prf → subst (˄ ψ γ) (cong (λ b → if b then ⟦ e₁ ⟧⊢ γ else ⟦ e₂ ⟧⊢ γ) (proj₂ ϕ-prf)) (prf γ (proj₁ ϕ-prf))) |
         e₂′ , e₂-≡ ← ref-completeness {ϕ = λ γ → ϕ γ × ⟦ c ⟧⊢ γ ≡ false}{ψ = ψ} e₂ (λ γ ϕ-prf → subst (˄ ψ γ) (cong (λ b → if b then ⟦ e₁ ⟧⊢ γ else ⟦ e₂ ⟧⊢ γ) (proj₂ ϕ-prf)) (prf γ (proj₁ ϕ-prf)))
    rewrite sym c-≡ | sym e₁-≡ | sym e₂-≡
    = IFᴿ c′ e₁′ e₂′ , refl
  ref-completeness {ϕ = ϕ}{ψ = ψ} (LET e₁ e₂) prf
    with e₁′ , e₁-≡ ← ref-completeness {ϕ = ϕ}{ψ = λ (γ , x) → x ≡ ⟦ e₁ ⟧⊢ γ} e₁ (λ _ _ → refl) |
         e₂′ , e₂-≡ ← ref-completeness {ϕ = λ (γ , x) → ϕ γ × x ≡ ⟦ e₁ ⟧⊢ γ}{ψ = λ ((γ , _) , t) → ψ (γ , t)} e₂ (λ (γ , s) (ϕ-prf , x-≡) → subst (λ x → ψ (γ , ⟦ e₂ ⟧⊢ (γ , x))) (sym x-≡) (prf γ ϕ-prf))
    rewrite e₁-≡ | sym e₂-≡
    = (LETᴿ {ϕ = ϕ}{ψ = ψ} e₁′ e₂′) , cong (λ x → LET x ⌜ e₂′ ⌝ᴿ) e₁-≡
  ref-completeness {ϕ = ϕ}{ψ = ψ} (PRD e₁ e₂) prf
    with e₁′ , e₁-≡ ← ref-completeness {ϕ = ϕ}{ψ = ᵏ ⊤} e₁ (λ _ _ → tt) |
         e₂′ , e₂-≡ ← ref-completeness {ϕ = ϕ}{ψ = ᵏ ⊤} e₂ (λ _ _ → tt)
    rewrite sym e₁-≡ | sym e₂-≡
    = SUBᴿ (PRDᴿ e₁′ e₂′) ψ (λ γ _ ϕ-prf x-≡ → subst (˄ ψ γ) (sym x-≡) (prf γ ϕ-prf)) , refl 
  ref-completeness {ϕ = ϕ}{ψ = ψ} (FST e) prf
    with e′ , e-≡ ← ref-completeness {ϕ = ϕ} e (λ _ _ → tt)
    rewrite sym e-≡
    = SUBᴿ (FSTᴿ e′) ψ (λ γ _ ϕ-prf x-≡ → subst (˄ ψ γ) (sym x-≡) (prf γ ϕ-prf)) , refl
  ref-completeness {ϕ = ϕ}{ψ = ψ} (SND e) prf
    with e′ , e-≡ ← ref-completeness {ϕ = ϕ} e (λ _ _ → tt)
    rewrite sym e-≡
    = SUBᴿ (SNDᴿ e′) ψ (λ γ _ ϕ-prf x-≡ → subst (˄ ψ γ) (sym x-≡) (prf γ ϕ-prf)) , refl
  ref-completeness {Γ = Γ}{ϕ = ϕ}{ψ = ψ} (APP f e) prf
    with f′ , f-≡ ← ref⃗-completeness {ξ = λ (γ , s) → s ≡ ⟦ e ⟧⊢ γ}{ψ = λ ((γ , s) , t) → t ≡ ⟦ f ⟧⊢⃗ γ s} f (λ _ _ _ → refl) |
         e′ , e-≡ ← ref-completeness {ϕ = ϕ}{ψ = λ (γ , s) → s ≡ ⟦ e ⟧⊢ γ} e (λ _ _ → refl)
    rewrite sym f-≡
    = (SUBᴿ (APPᴿ f′ e′) _ λ γ t ϕ-prf t-≡ → subst (˄ ψ γ) (sym t-≡) (subst (λ x → ψ (γ , ⟦ f ⟧⊢⃗ γ (⟦ x ⟧⊢ γ))) (sym e-≡) (prf γ ϕ-prf))) , icong {f = APP ⌜ f′ ⌝ᴿ⃗} e-≡
  ref-completeness {ϕ = ϕ}{ψ = ψ} (BOP o e₁ e₂) prf
    with e₁′ , e₁-≡ ← ref-completeness {ϕ = ϕ} e₁ (λ _ _ → tt) |
         e₂′ , e₂-≡ ← ref-completeness {ϕ = ϕ} e₂ (λ _ _ → tt)
    rewrite sym e₁-≡ | sym e₂-≡
    = SUBᴿ (BOPᴿ o e₁′ e₂′) ψ (λ γ _ ϕ-prf x-≡ → subst (˄ ψ γ) (sym x-≡) (prf γ ϕ-prf)) , refl

  ref⃗-completeness {ϕ = ϕ}{ξ = ξ}{ψ = ψ} (FUN e) prf
    with e′ , e-≡ ← ref-completeness e (λ (γ , s) ξ-prf → prf γ s ξ-prf)
    rewrite sym e-≡ = (FUNᴿ e′) , refl
\end{code}

With the refinement soundness and completeness theorems, we can deduce a few direct but useful corollaries.
%
\begin{corollary}
Refinement soundness holds for closed terms.
\end{corollary}

\begin{corollary}
For refinement typing judgements, the predicate $ϕ$ over the context is an invariant, namely,
$Γ;ϕ ⊢_R \hat{e} : \RefTy{ν}{T}{λ ν. \, ϕ}$.
\end{corollary}


\begin{code}[hide]
  pre-inv : ∀{Γ}{T}{ϕ} → (e : Γ ⊢ T)
          → Σ (Γ ❴ ϕ ❵⊢ T ❴ ϕ ∘ proj₁ ❵) λ e′ → ⌜ e′ ⌝ᴿ ≡ e
  pre-inv e = ref-completeness e (λ γ ϕ-prf → ϕ-prf)
\end{code}

\begin{corollary}[Consistency]
It is impossible to assign a void refinement type to an expression $\hat{Γ} ⊢_R \hat{e} : \RefTy{ν}{T}{\FF}$,
if there exists a semantic environment $γ$ that respects $\hat{Γ}$.
\end{corollary}

\begin{code}[hide]
  consistency : ∀{Γ}{T}{ϕ}
              → (e : Γ ❴ ϕ ❵⊢ T ❴ ᵏ ⊥ ❵)
              → Σ ⟦ Γ ⟧C ϕ
              → ⊥
  consistency e (γ , ϕ-prf) = ref-soundness e ϕ-prf
\end{code}


\section{Typechecking \reflang by Weakest Precondition} \label{sec:wp}

A na\"ive typechecking algorithm can be given to the \reflang language,
in terms of the weakest precondition predicate transformer~\citep{Dijkstra_75}.
Since all functions in \reflang are required to be annotated with types,
it is possible to assume the postcondition of a function and
compute the weakest precondition. If the given precondition in the type signature
entails the weakest precondition, we know that the program is well-typed
according to the specification (i.e.\ the type signature).

In an imperative language, when a variable $x$ gets assigned, the Hoare triple
is $\{ Q[e/x] \}\ x := e\ \{ Q \}$, which means that the weakest precondition can be
obtained by simply substituting the variable $x$ in $Q$ by the expression $e$.
The Hoare logic style typing judgement $Γ ❴ ϕ ❵⊢ e : T ❴ ψ ❵$ in our
purely functional language can be considered as assigning the value of $e$ to a fresh variable $ν$.
Therefore the weakest precondition function $\wpc\ ψ\ e$ can be defined analogously
as a substitution of the top binder $ν$ in $ψ$ with the value of $e$, resulting in a predicate over
a semantic environment $γ$ that respects $Γ$.
\begin{center}
\begin{code}
  wp : ∀{Γ}{T} → (⟦ Γ ▸ T ⟧C → Set) → Γ ⊢ T → (⟦ Γ ⟧C → Set)
  wp ψ e = ψ [ e ]s
\end{code}
\end{center}

The completeness and soundness of the $\wpc$ function with respect to
the typing rules of \reflang are direct corollaries of the
refinement soundness and completeness theorems (\cref{thm:ref-soundness} and
\cref{thm:ref-completeness}) respectively.

\begin{theorem}[Completeness of $\wpc$ w.r.t. \reflang typing]
If $Γ; ϕ ⊢_R \hat{e} : \RefTy{ν}{T}{ψ}$, then $ϕ\ γ ⇒ \wpc\ ψ\ ⌜ \hat{e} ⌝ᴿ\ γ$
for any semantic environment $γ$ that respects $Γ$.
\end{theorem}

\begin{theorem}[Soundness of $\wpc$ w.r.t. \reflang typing]
For an expression $Γ ⊢ e : T$ in \baselang and a predicate $ψ$,
there must exist a type derivation $Γ; \wpc\ ψ\ e ⊢_R \hat{e} : \RefTy{ν}{T}{ψ}$
such that $⌜ \hat{e} ⌝ᴿ = e$.
\end{theorem}

\begin{code}[hide]
  wp⃗ : ∀{Γ}{S T} → (⟦ Γ ▸ S ▸ T ⟧C → Set) → Γ ⊢ S ⟶ T → (⟦ Γ ▸ S ⟧C → Set)
  wp⃗ ψ (FUN e) = wp ψ e

  wp-completeness : ∀{Γ}{T}{ϕ}{ψ}
                  → (e : Γ ❴ ϕ ❵⊢ T ❴ ψ ❵)
                  → (γ : ⟦ Γ ⟧C)
                  → (ϕ γ → wp ψ ⌜ e ⌝ᴿ γ)
  wp-completeness e γ = ref-soundness e

  wp-soundness : ∀{Γ}{T}
               → (e : Γ ⊢ T)
               → (ψ : ⟦ Γ ▸ T ⟧C → Set)
               → Σ (Γ ❴ wp ψ e ❵⊢ T ❴ ψ ❵) λ e′ → ⌜ e′ ⌝ᴿ ≡ e
  wp-soundness e ψ = ref-completeness {ϕ = wp ψ e} e (λ _ wp → wp)
\end{code}

The $\wpc$ function checks that, when a type signature is given to an expression $e$,
it can infer the weakest precondition under which $e$ is typeable. Writing
in natural deduction style, the algorithmic typing rule looks like:
$$
\inferrule
  { ⋯ }
  {Γ;ϕ \vdashalg e : \RefTy{ν}{T}{ψ}}
$$
Contrary to regular algorithmic typing rules (e.g.\ in bidirectional
typing~\citep{Dunfield_Krishnaswaim_21}), where the context and the expression are
typically inputs, and the type is either input or output depending on whether
it performs type checking or synthesise, in our formulation, the expression and the type
are the inputs and (the predicate part of) the context is the output.

The $\wpc$ function only checks whether an expression is well-typed by inferring the weakest
context, but it does not elaborate the typing tree by annotating each sub-expression with
a type, nor does it automatically construct proof terms.
Despite the limitation, this method can still be applied to program verification
tasks in which the exact refinement typing tree need not be constructed, or when the automatic construction
of proof terms is not required. For instance, we intend to augment
the \cogent language~\citep{OConnor_CRALMNSK_16, OConnor:phd, OConnor_CRJAKMSK_21},
a purely functional language for the ease of formal verification of systems code, with
refinement types. In \cogent's verification framework, a fully elaborated refinement typing tree
will not be necessary, and the functional correctness
of a system is manually proved in Isabelle/HOL. Since proof engineers are already
engaged, we do not have to rely on an SMT-solver to fully construct the proof objects.
It is a bonus, but not a prerequisite.

\section{Function Contracts with \complang} \label{sec:comp-lang}

As we have seen, $\wpc$ is easy to define and works uniformly across all terms.
Yet it has
a very unfortunate drawback---it is defined on the simply-typed language and is oblivious to
the function signatures, and consequently does not preserve function contracts. This is however
not the only problem. In the definition of $\wpc$, when it is applied to an expression containing function
applications,
instead of β-reducing the applications, it should inspect the function's type signature and
produce verification conditions for the function contracts.
To this end, the denotation function $\denotTm{\cdot}$ and subsequently the refinement typing
rules also need to be revised.

We define a variant of the language \complang, in which 
the function contracts are respected.\footnote{The superscript $C$ in \complang means ``contract''.}
It is worth mentioning that the language is not yet compositional in the sense of \citep{Knowles_Flanagan_09},
as the weakest precondition computation still draws information from the implementation of
expressions, which we will see later in this section.

\subsection{The \complang Language}

The syntax of \complang is the same as \reflang, and its typing rules are very similar to those
of \reflang as well. Despite the fact that the \complang language will reflect its term
language to Agda in a slightly different way (more details in \autoref{ssec:ann-lang}), we only make two changes in the typing rules for \complang:

\begin{inductive}{\hat{Γ} ⊢_C \hat{e} : τ}
\inferrule
  {Γ; ϕ ⊢_C \hat{e}₁ : \RefTy{x}{S}{ξ} \\
   \wf{Γ ⊢ \RefTy{ν}{T}{ψ}} \\\\
   Γ, x:S; ϕ ∧ x = \hat{e}₁ ⊢_C \hat{e}₂ : \RefTy{ν}{T}{ψ}}
  {Γ; ϕ ⊢_C \LET\ x = \hat{e}₁\ \IN\ \hat{e}₂ : \RefTy{ν}{T}{ψ}}
  {\textsf{LETᶜ}}
\\
\inferrule
  {Γ; ϕ ⊢_C \hat{f} : \RefFunTy{x}{\RefTy{ν}{S}{ξ}}{\RefTy{ν}{T}{ψ}} \\\\
   x ∉ \textsf{Dom}(Γ) \\
   Γ; ϕ ⊢_C \hat{e} : \RefTy{ν}{S}{ξ}}
  {Γ; ϕ ⊢_C \hat{f}\ \hat{e} : \RefTy{ν}{T}{∃ x:ξ[x/ν]. ψ}}
  {\textsf{APPᶜ}}
\end{inductive}

As suggested by \citet{Knowles_Flanagan_09}, the result of a function application can be
made existential for retaining the abstraction over the function's argument. This idea is
implemented as the rule \textsf{APPᶜ}. The choice of using this favour of function application
is purely incidental---offering a contrast to the other variant used in \reflang. In practice,
we believe both rules have their place in a system. The existential version is significantly limited
in the conclusions that it can lead to, and renders some basic functions useless. For instance,
we define an $\textsf{inc}$ function as follows:
%
{\csp
\begin{align*}
& \textsf{inc} : \MyDepFunTy{x}{ℕ}{\RefTy{ν}{ℕ}{ν = x + 1}} \\
& \textsf{inc} = λ x.\,x + 1
\end{align*}}

The function's output is already giving the exact type of the result.
With the $\textsf{APPᶜ}$ rule, we cannot deduce that $\textsf{inc}\ 0$ is 1, which is
intuitively very obvious. In fact, if the input type of $\textsf{inc}$ is kept unrefined,
then we can hardly draw any conclusion about the result of this function. This behaviour
can be problematic when users define, say, arithmetic operations as functions.

The $\textsf{LETᶜ}$ rule differs from $\textsf{LETᴿ}$ in a
way that the precondition of the expression $e₂$ is $ϕ$ in conjunction with the exact refinement
$x = \hat{e}₁$ for the new binder $x$ instead of the arbitrary postcondition $ξ$ of $e₁$.
Intuitively, because the exact type of the local binder is added to the
context when typechecking $e₂$, when we compute the weakest precondition
of the let-expression (later in \autoref{fig:pre-def}), we can assume the trivial
postcondition $λ\_.\, \TT$ of $e₁$. This makes the \textsf{LETᶜ} rule
significantly easier to work with.
Unfortunately, we do not yet have formal evidence to conclude with full confidence whether the \textsf{LETᴿ} rule
can be used in this system instead of \textsf{LETᶜ} or not. Also note that,
\textsf{LETᶜ} gives
different reasoning power than \textsf{APPᶜ} does, and they nicely complement
each other in the system.


\begin{code}[hide]
module Refinementᶜ where

  open Refinement using (_⊨_⇒_)

  infix 10 _⊢ᴬ_

  data _⊢ᴬ_ (Γ : Cx) : U → Set₁
  data _⊢ᴬ_❴_❵⟶_❴_❵ (Γ : Cx) : (S : U)
                               → (⟦ Γ ▸ S ⟧C → Set)
                               → (T : U)
                               → (⟦ Γ ▸ S ▸ T ⟧C → Set)
                               → Set₁

  data _⊢ᴬ_ Γ where
    VARᴬ   : ∀{T} → Γ ∋ T → Γ ⊢ᴬ T
    UNITᴬ  : Γ ⊢ᴬ ‵1′
    TTᴬ    : Γ ⊢ᴬ ‵2′
    FFᴬ    : Γ ⊢ᴬ ‵2′
    ZEᴬ    : Γ ⊢ᴬ ‵ℕ′
    SUᴬ    : Γ ⊢ᴬ ‵ℕ′ → Γ ⊢ᴬ ‵ℕ′
    IFᴬ    : ∀{T} → Γ ⊢ᴬ ‵2′ → Γ ⊢ᴬ T → Γ ⊢ᴬ T → Γ ⊢ᴬ T
    LETᴬ   : ∀{S T} → Γ ⊢ᴬ S → Γ ▸ S ⊢ᴬ T → Γ ⊢ᴬ T
    PRDᴬ   : ∀{S T} → Γ ⊢ᴬ S → Γ ⊢ᴬ T → Γ ⊢ᴬ (S ‵×′ T)
    FSTᴬ   : ∀{S T} → Γ ⊢ᴬ S ‵×′ T → Γ ⊢ᴬ S
    SNDᴬ   : ∀{S T} → Γ ⊢ᴬ S ‵×′ T → Γ ⊢ᴬ T
    APPᴬ   : ∀{S T}{ξ}{ψ} → Γ ⊢ᴬ S ❴ ξ ❵⟶ T ❴ ψ ❵ → Γ ⊢ᴬ S → Γ ⊢ᴬ T
    BOPᴬ   : (o : ⊕) → Γ ⊢ᴬ →⊕ o → Γ ⊢ᴬ →⊕ o → Γ ⊢ᴬ ⊕→ o
  
  data _⊢ᴬ_❴_❵⟶_❴_❵ Γ where
    FUNᴬ : ∀{S T}{ξ}{ψ} → Γ ▸ S ⊢ᴬ T → Γ ⊢ᴬ S ❴ ξ ❵⟶ T ❴ ψ ❵

\end{code}

\newcommand{\postulateDelta}{%
\begin{code}
  postulate
    δ : ∀{Γ}{S T}{ξ}{ψ} → Γ ⊢ᴬ S ❴ ξ ❵⟶ T ❴ ψ ❵
                        → ⟦ Γ ⟧C → ⟦ S ⟧τ → ⟦ T ⟧τ
\end{code}}


\begin{code}[hide]
  ⟦_⟧⊢ᴬ : ∀{Γ}{T} → Γ ⊢ᴬ T → ⟦ Γ ⟧C → ⟦ T ⟧τ
  ⟦_⟧⊢ᴬ⃗ : ∀{Γ}{S T}{ξ}{ψ} → Γ ⊢ᴬ S ❴ ξ ❵⟶ T ❴ ψ ❵
        → ⟦ Γ ⟧C → ⟦ S ⟧τ → ⟦ T ⟧τ

  ⟦ VARᴬ x ⟧⊢ᴬ = ⟦ x ⟧∋
  ⟦ UNITᴬ ⟧⊢ᴬ = ᵏ tt
  ⟦ TTᴬ ⟧⊢ᴬ = ᵏ true
  ⟦ FFᴬ ⟧⊢ᴬ = ᵏ false
  ⟦ ZEᴬ ⟧⊢ᴬ = ᵏ 0
  ⟦ SUᴬ e ⟧⊢ᴬ = ᵏ suc ˢ ⟦ e ⟧⊢ᴬ
  ⟦ IFᴬ c e₁ e₂ ⟧⊢ᴬ = (if_then_else_ ∘ ⟦ c ⟧⊢ᴬ) ˢ ⟦ e₁ ⟧⊢ᴬ ˢ ⟦ e₂ ⟧⊢ᴬ
  ⟦ LETᴬ e₁ e₂ ⟧⊢ᴬ = ˄ ⟦ e₂ ⟧⊢ᴬ ˢ ⟦ e₁ ⟧⊢ᴬ
  ⟦ PRDᴬ e₁ e₂ ⟧⊢ᴬ = < ⟦ e₁ ⟧⊢ᴬ , ⟦ e₂ ⟧⊢ᴬ >
  ⟦ FSTᴬ e ⟧⊢ᴬ = proj₁ ∘ ⟦ e ⟧⊢ᴬ
  ⟦ SNDᴬ e ⟧⊢ᴬ = proj₂ ∘ ⟦ e ⟧⊢ᴬ
  ⟦ APPᴬ f e ⟧⊢ᴬ = ⟦ f ⟧⊢ᴬ⃗ ˢ ⟦ e ⟧⊢ᴬ
  ⟦ BOPᴬ o e₁ e₂ ⟧⊢ᴬ = ᵏ (⟦⟧⊢⊕ o) ˢ ⟦ e₁ ⟧⊢ᴬ ˢ ⟦ e₂ ⟧⊢ᴬ
\end{code}


\subsection{Annotated Base Language \annlang} \label{ssec:ann-lang}

To typecheck of \complang, we define \annlang, a variant of the base language
\baselang. It differs in that the
functions are accompanied by type signatures.
We denote function expressions in \annlang as $f ∷ \MyDepFunTy{x}{ξ}{ψ}$, instead of
a bare unrefined $f$.


To establish the connection between \complang and \annlang, an erasure
function $⌜\cdot⌝ᶜ$ is defined, taking a \complang term to the corresponding
\annlang term.
It preserves the function's type annotations in \complang,
so that we know that when a \annlang term is typed, the functions are typed
in accordance with their type signatures.

One reason why \reflang does not preserve the function contracts
is because the way we interpret function calls. Imagine an expression
$((f ∷ \MyDepFunTy{x}{ξ}{ψ})\ 1) + 2$ in the language \complang
where $f ≡ λx.\, x + 1$, $ξ ≡ λ x.\, x < 2$ and $ψ ≡ λ ν.\, ν < 4$,
which is well-typed.
Ideally, the only knowledge that we can learn about the
function application should be drawn from its type signature, namely
$λ ν.\,ν < 4$ here. Therefore, the most precise type we can assign
to the whole
expression is $\RefTy{ν}{ℕ}{ν < 6}$.
However, according to the typing rule \textsf{ADDᶜ},
the inferred refinement predicate of the result of the addition will be
an Agda term $\denotTm{\FunN{f}\ 1}γ + \denotTm{2}γ$ for any $γ$.
As the predicate reduces in Agda, it means that we can in fact conclude that
the result is equal to $4$, which is more precise than
what the function contract tells us---we again lost the abstraction over $f$.

\newcommand{\interpretFc}{%
\begin{code}
  ⟦ f ⟧⊢ᴬ⃗ = δ f
\end{code}}

To fix the problem, we revise the definition of $\denotTm{\cdot}$.
Instead of interpreting functions as their Agda shallow embedding,
we \AgdaKeyword{postulate}{} the interpretation of functions as $δ$:

\begin{center}
\AgdaNoSpaceAroundCode{%
\postulateDelta}
\end{center}

It allows us to reflect functions in the object language into the logic
as uninterpreted functions. In the example above, it will stop
the shallow postcondition from reducing to $4$, retaining a symbolic
representation of the function $f$.
We define a new interpretation function
$\denotTmA{\cdot}$ for \annlang terms
(\AgdaFunction{⟦}\AgdaUnderscore\AgdaOperator{\AgdaFunction{⟧⊢ᴬ}}
and \AgdaFunction{⟦}\AgdaUnderscore\AgdaOperator{\AgdaFunction{⟧⊢ᴬ⃗}}
in the Agda formalisation). It is defined in the same way as
$\denotTm{\cdot}$, with the exception of functions:

\begin{center}
\AgdaNoSpaceAroundCode{%
\interpretFc}
\end{center}



\begin{code}[hide]
  _[_]sᶜ : ∀{Γ}{T} → (ϕ : ⟦ Γ ▸ T ⟧C → Set) → (e : Γ ⊢ᴬ T)
         → (⟦ Γ ⟧C → Set)
  ϕ [ e ]sᶜ = ˄ ϕ ˢ ⟦ e ⟧⊢ᴬ

  -- Compositional HL.
  data _❴_❵⊢ᶜ_❴_❵ (Γ : Cx) : (⟦ Γ ⟧C → Set) → (T : U) → (⟦ Γ ▸ T ⟧C → Set) → Set₁

  data _❴_❵⊢ᶜ_❴_❵⟶_❴_❵ (Γ : Cx) : (⟦ Γ ⟧C → Set)
                                → (S : U)
                                → (⟦ Γ ▸ S ⟧C → Set)
                                → (T : U)
                                → (⟦ Γ ▸ S ▸ T ⟧C → Set)
                                → Set₁


  ⌜_⌝ᶜ : ∀{Γ}{T}{ϕ}{ψ} → Γ ❴ ϕ ❵⊢ᶜ T ❴ ψ ❵ → Γ ⊢ᴬ T
  ⌜_⌝ᶜ⃗ : ∀{Γ}{S T}{ϕ}{ξ}{ψ}
        → Γ ❴ ϕ ❵⊢ᶜ S ❴ ξ ❵⟶ T ❴ ψ ❵
        → Γ ⊢ᴬ S ❴ ξ ❵⟶ T ❴ ψ ❵

  data _❴_❵⊢ᶜ_❴_❵ Γ where
    VARᶜ   : ∀{ϕ}{T} → (i : Γ ∋ T) → Γ ❴ ϕ ❵⊢ᶜ T ❴ (λ (γ , ν) → ν ≡ ⟦ i ⟧∋ γ) ❵
    UNITᶜ  : ∀{ϕ} → Γ ❴ ϕ ❵⊢ᶜ ‵1′ ❴ (λ γ → proj₂ γ ≡ tt) ❵
    TTᶜ    : ∀{ϕ} → Γ ❴ ϕ ❵⊢ᶜ ‵2′ ❴ (λ γ → proj₂ γ ≡ true ) ❵
    FFᶜ    : ∀{ϕ} → Γ ❴ ϕ ❵⊢ᶜ ‵2′ ❴ (λ γ → proj₂ γ ≡ false) ❵
    ZEᶜ    : ∀{ϕ} → Γ ❴ ϕ ❵⊢ᶜ ‵ℕ′ ❴ (λ γ → proj₂ γ ≡ 0 ) ❵
    SUᶜ    : ∀{ϕ}{ψ}
           → (n : Γ ❴ ϕ ❵⊢ᶜ ‵ℕ′ ❴ ψ ❵)
           → Γ ❴ ϕ ❵⊢ᶜ ‵ℕ′ ❴ (λ (γ , ν) → ν ≡ suc (⟦ ⌜ n ⌝ᶜ ⟧⊢ᴬ γ)) ❵
    IFᶜ    : ∀{ϕ}{ξ}{T}{ψ}
           → (c : Γ ❴ ϕ ❵⊢ᶜ ‵2′ ❴ ξ ❵)
           → (Γ ❴ (λ γ → ϕ γ × ⟦ ⌜ c ⌝ᶜ ⟧⊢ᴬ γ ≡ true ) ❵⊢ᶜ T ❴ ψ ❵)
           → (Γ ❴ (λ γ → ϕ γ × ⟦ ⌜ c ⌝ᶜ ⟧⊢ᴬ γ ≡ false) ❵⊢ᶜ T ❴ ψ ❵)
           → Γ ❴ ϕ ❵⊢ᶜ T ❴ ψ ❵
    LETᶜ   : ∀{S}{T}{ϕ}{ξ : ⟦ Γ ▸ S ⟧C → Set}{ψ : ⟦ Γ ▸ T ⟧C → Set}
           → (e₁ : Γ ❴ ϕ ❵⊢ᶜ S ❴ ξ ❵)
           → (e₂ : (Γ ▸ S) ❴ (λ (γ , s) → ϕ γ × s ≡ ⟦ ⌜ e₁ ⌝ᶜ ⟧⊢ᴬ γ) ❵⊢ᶜ T ❴ (λ ((γ , _) , t) → ψ (γ , t)) ❵)
           → Γ ❴ ϕ ❵⊢ᶜ T ❴ ψ ❵
    PRDᶜ   : ∀{S T}{ϕ}{ψ₁ ψ₂}
           → (e₁ : Γ ❴ ϕ ❵⊢ᶜ S ❴ ψ₁ ❵)
           → (e₂ : Γ ❴ ϕ ❵⊢ᶜ T ❴ ψ₂ ❵)
           → Γ ❴ ϕ ❵⊢ᶜ S ‵×′ T ❴ (λ (γ , ν) → ν ≡ < ⟦ ⌜ e₁ ⌝ᶜ ⟧⊢ᴬ , ⟦ ⌜ e₂ ⌝ᶜ ⟧⊢ᴬ > γ) ❵
    FSTᶜ   : ∀{S T}{ϕ}{ψ}
           → (e : Γ ❴ ϕ ❵⊢ᶜ S ‵×′ T ❴ ψ ❵)
           → Γ ❴ ϕ ❵⊢ᶜ S ❴ (λ (γ , ν) → ν ≡ proj₁ (⟦ ⌜ e ⌝ᶜ ⟧⊢ᴬ γ)) ❵
    SNDᶜ   : ∀{S T}{ϕ}{ψ}
           → (e : Γ ❴ ϕ ❵⊢ᶜ S ‵×′ T ❴ ψ ❵)
           → Γ ❴ ϕ ❵⊢ᶜ T ❴ (λ (γ , ν) → ν ≡ proj₂ (⟦ ⌜ e ⌝ᶜ ⟧⊢ᴬ γ)) ❵
    APPᶜ   : ∀{S}{T}{ϕ}{ξ}{ψ}
           → (f : Γ ❴ ϕ ❵⊢ᶜ S ❴ ξ ❵⟶ T ❴ ψ ❵)
           → (e : Γ ❴ ϕ ❵⊢ᶜ S ❴ ξ ❵)
           → Γ ❴ ϕ ❵⊢ᶜ T ❴ (λ (γ , t) → Σ ⟦ S ⟧τ λ s → ξ (γ , s) × ψ ((γ , s) , t)) ❵
    BOPᶜ   : ∀{ϕ}(o : ⊕){ψ₁ ψ₂}
           → (e₁ : Γ ❴ ϕ ❵⊢ᶜ →⊕ o ❴ ψ₁ ❵)
           → (e₂ : Γ ❴ ϕ ❵⊢ᶜ →⊕ o ❴ ψ₂ ❵)
           → Γ ❴ ϕ ❵⊢ᶜ ⊕→ o ❴ (λ (γ , ν) → ν ≡ ⟦ ⌜ e₁ ⌝ᶜ ⟧⊢ᴬ γ ⟦ o ⟧⊢⊕ ⟦ ⌜ e₂ ⌝ᶜ ⟧⊢ᴬ γ) ❵
    SUBᶜ   : ∀{T}{ϕ : ⟦ Γ ⟧C → Set}{ψ : ⟦ Γ ▸ T ⟧C → Set}
           → (e : Γ ❴ ϕ ❵⊢ᶜ T ❴ ψ ❵)
           → (ψ′ : ⟦ Γ ▸ T ⟧C → Set)
           → ϕ ⊨ ψ ⇒ ψ′
           → Γ ❴ ϕ ❵⊢ᶜ T ❴ ψ′ ❵

  data _❴_❵⊢ᶜ_❴_❵⟶_❴_❵ Γ where
    FUNᶜ   : ∀{S T}{ϕ}{ξ}{ψ}
           → Γ ▸ S ❴ (λ (γ , s) → ϕ γ × ξ (γ , s)) ❵⊢ᶜ T ❴ ψ ❵
           → Γ ❴ ϕ ❵⊢ᶜ S ❴ ξ ❵⟶ T ❴ ψ ❵


  ⌜ VARᶜ i ⌝ᶜ = VARᴬ i
  ⌜ UNITᶜ ⌝ᶜ = UNITᴬ
  ⌜ TTᶜ ⌝ᶜ = TTᴬ
  ⌜ FFᶜ ⌝ᶜ = FFᴬ
  ⌜ ZEᶜ ⌝ᶜ = ZEᴬ
  ⌜ SUᶜ n ⌝ᶜ = SUᴬ ⌜ n ⌝ᶜ
  ⌜ IFᶜ c e₁ e₂ ⌝ᶜ = IFᴬ ⌜ c ⌝ᶜ ⌜ e₁ ⌝ᶜ ⌜ e₂ ⌝ᶜ
  ⌜ LETᶜ e₁ e₂ ⌝ᶜ = LETᴬ ⌜ e₁ ⌝ᶜ ⌜ e₂ ⌝ᶜ
  ⌜ PRDᶜ e₁ e₂ ⌝ᶜ = PRDᴬ ⌜ e₁ ⌝ᶜ ⌜ e₂ ⌝ᶜ
  ⌜ FSTᶜ e ⌝ᶜ = FSTᴬ ⌜ e ⌝ᶜ
  ⌜ SNDᶜ e ⌝ᶜ = SNDᴬ ⌜ e ⌝ᶜ
  ⌜ APPᶜ f e ⌝ᶜ = APPᴬ ⌜ f ⌝ᶜ⃗ ⌜ e ⌝ᶜ
  ⌜ BOPᶜ o e₁ e₂ ⌝ᶜ = BOPᴬ o ⌜ e₁ ⌝ᶜ ⌜ e₂ ⌝ᶜ
  ⌜ SUBᶜ e ψ′ _ ⌝ᶜ = ⌜ e ⌝ᶜ

  ⌜ FUNᶜ e ⌝ᶜ⃗ = FUNᴬ ⌜ e ⌝ᶜ

\end{code}

\newcommand{\mkContract}{%
\begin{code}
  mkC : ∀{Γ}{S T}{ξ}{ψ} → Γ ⊢ᴬ S ❴ ξ ❵⟶ T ❴ ψ ❵ → Set
  mkC {Γ = Γ}{S = S}{ξ = ξ}{ψ = ψ} f =
    {γ : ⟦ Γ ⟧C} → (x : ⟦ S ⟧τ) → ξ (γ , x) → ψ ((γ , x) , δ f γ x)
\end{code}}

\begin{code}[hide]
  module _ where
    private postulate
      δ≡⟦⟧⊢ : ∀{Γ}{γ : ⟦ Γ ⟧C}{S T}{ξ}{ψ}
           → (e : Γ ▸ S ⊢ᴬ T)
           → (x : ⟦ S ⟧τ)
           → δ (FUNᴬ {ξ = ξ}{ψ = ψ} e) γ x ≡ ⟦ e ⟧⊢ᴬ (γ , x)
  
    refᶜ-soundness : ∀{Γ}{ϕ}{γ : ⟦ Γ ⟧C}{T}{ψ}
                  → (e : Γ ❴ ϕ ❵⊢ᶜ T ❴ ψ ❵)
                  → (ϕ γ → ψ (γ , ⟦ ⌜ e ⌝ᶜ ⟧⊢ᴬ γ))
    refᶜ⃗-soundness : ∀{Γ}{γ : ⟦ Γ ⟧C}{S T}{ϕ}{ξ}{ψ}
                   → (f : Γ ❴ ϕ ❵⊢ᶜ S ❴ ξ ❵⟶ T ❴ ψ ❵)
                   → (x : ⟦ S ⟧τ) → ϕ γ → ξ (γ , x) → ψ ((γ , x) , ⟦ ⌜ f ⌝ᶜ⃗ ⟧⊢ᴬ⃗ γ x)
  
    refᶜ-soundness (VARᶜ _) _ = refl
    refᶜ-soundness UNITᶜ _ = refl
    refᶜ-soundness TTᶜ _ = refl
    refᶜ-soundness FFᶜ _ = refl
    refᶜ-soundness ZEᶜ _ = refl
    refᶜ-soundness (SUᶜ _) _ = refl
    refᶜ-soundness {γ = γ} (IFᶜ c e₁ e₂) ϕ-prf with ⟦ ⌜ c ⌝ᶜ ⟧⊢ᴬ γ in cond
    ... | true  = refᶜ-soundness e₁ (ϕ-prf , cond)
    ... | false = refᶜ-soundness e₂ (ϕ-prf , cond)
    refᶜ-soundness (LETᶜ e₁ e₂) ϕ-prf = refᶜ-soundness e₂ (ϕ-prf , refl)
    refᶜ-soundness (PRDᶜ _ _) _ = refl
    refᶜ-soundness (FSTᶜ _) _ = refl
    refᶜ-soundness (SNDᶜ _) _ = refl
    refᶜ-soundness {γ = γ}(APPᶜ f e) ϕ-prf
      = (⟦ ⌜ e ⌝ᶜ ⟧⊢ᴬ γ) , (refᶜ-soundness e ϕ-prf , refᶜ⃗-soundness f (⟦ ⌜ e ⌝ᶜ ⟧⊢ᴬ γ) ϕ-prf (refᶜ-soundness e ϕ-prf))
    refᶜ-soundness (BOPᶜ _ _ _) _ = refl
    refᶜ-soundness {γ = γ} (SUBᶜ e _ sub) ϕ-prf = sub γ (⟦ ⌜ e ⌝ᶜ ⟧⊢ᴬ γ) ϕ-prf (refᶜ-soundness e ϕ-prf)
  
    refᶜ⃗-soundness {γ = γ} (FUNᶜ {ξ = ξ}{ψ = ψ} e) x ϕ-prf ξ-prf
      rewrite δ≡⟦⟧⊢ {γ = γ}{ξ = ξ}{ψ = ψ} ⌜ e ⌝ᶜ x
      = refᶜ-soundness e (ϕ-prf , ξ-prf)
  
    refᶜ-soundness′ : ∀{T}{ψ}
                   → (e : ‵Ε′ ❴ ᵏ ⊤ ❵⊢ᶜ T ❴ ψ ❵)
                   → ψ (tt , ⟦ ⌜ e ⌝ᶜ ⟧⊢ᴬ tt)
    refᶜ-soundness′ e = refᶜ-soundness e tt    
\end{code}


On the other hand, when we type any expressions in the language \complang,
we need to add the known function contracts to
the precondition $ϕ$. The function contract can be extracted automatically
by a $\AgdaFunction{mkC}$ function defined as follows:

\begin{center}
\AgdaNoSpaceAroundCode{%
\mkContract}
\end{center}


\subsection{Typechecking \annlang}

In order to typecheck \annlang, which is a language that is already well-typed
with respect to simple types, and all functions are annotated with refinement types,
we want to have a similar deterministic procedure as we had in \autoref{sec:wp}.
Unfortunately, in the presence of the function boundaries, the weakest precondition
computation cannot be done simply by substituting in the expressions.

We borrow the ideas from computing weakest preconditions for imperative languages with loops.
Specifically, we follow the development found in \citet[\S{}12.4]{Nipkow_Klein:Isabelle}'s book.
In standard Hoare logic, it is widely known that the loop-invariant for a \textsf{WHILE}-loop
cannot be computed using the weakest precondition function $\wpc$~\citep{Dijkstra_75}, as the function
is recursive and may not terminate.
In \citet{Nipkow_Klein:Isabelle}'s work, for Isabelle/HOL to deterministically generate the verification condition
for a Hoare triple, it requires the users to provide annotations for loop-invariants.
It then divides the standard $\wpc$ function
into two functions: $\textsf{pre}$ and $\textsf{vc}$. The former computes the weakest precondition nearly as $\wpc$,
except that in the case of a \textsf{WHILE}-loop, it returns the annotated invariant immediately. The latter then
checks that the provided invariants indeed make sense. Intuitively, for a \textsf{WHILE}-loop, it checks that
the invariant $I$ together with the loop condition implies the precondition of the loop body,
which needs to preserve $I$ afterwards, and that $I$ together with the negation of the loop-condition
implies the postcondition. In all other cases, the $\textsf{vc}$ function simply recurses down the sub-statements
and aggregates verification conditions.

Although there is no recursion---the functional counterparts to loops of an imperative language---%
in our language, the situation with functions is somewhat similar to \textsf{WHILE}-loops. We also cannot
compute the weakest precondition according to the expressions, but have to rely on user annotations,
for a different reason. We can also divide the $\wpc$ computation into $\pre$ and $\vc$.
The function $\pre$ immediately returns the precondition of a function, which is the refinement predicate of
the argument type. Then $\vc$ additionally validates the provided function signatures.
In particular, we need to check that in a function application:
\begin{enumerate*}[label=(\arabic*)]
  \item the function's actual argument is of a supertype to the prescribed input type;
  \item the function's prescribed output type implies the postcondition of the function application inferred 
  from the program context.
\end{enumerate*}
Additionally, $\vc$ needs to recurse down the syntax tree and gather verification conditions
from sub-expressions, and, in particular, descend into the function definition to check that it
meets the given type signature. The definitions of the $\pre$ and the $\vc$ functions
are shown in \autoref{fig:pre-def} and \autoref{fig:vc-def} respectively.%
\footnote{$∩$ is the intersection of predicates defined in Agda's
standard library as: $P ∩ Q = λ γ → P\ γ × Q\ γ$.}


\newcommand{\preDef}{%
\begin{code}
  pre  : ∀{Γ}{T}(ψ : ⟦ Γ ▸ T ⟧C → Set) → (e : Γ ⊢ᴬ T)
       → (⟦ Γ ⟧C → Set)
  pre⃗ : ∀{Γ}{S T}{ξ}{ψ} → Γ ⊢ᴬ S ❴ ξ ❵⟶ T ❴ ψ ❵
       → (⟦ Γ ▸ S ⟧C → Set)

  pre ψ (SUᴬ e) = pre (ᵏ ⊤) e ∩ ψ [ SUᴬ e ]sᶜ
  pre ψ (IFᴬ c e₁ e₂)
    = pre (ᵏ ⊤) c
    ∩ (if_then_else_ ∘ ⟦ c ⟧⊢ᴬ) ˢ pre ψ e₁ ˢ pre ψ e₂
  pre ψ (LETᴬ e₁ e₂)
    = pre (ᵏ ⊤) e₁
    ∩ ˄ (pre (λ ((γ , _) , t) → ψ (γ , t)) e₂) ˢ ⟦ e₁ ⟧⊢ᴬ
  pre ψ (PRDᴬ e₁ e₂)
    = pre (ᵏ ⊤) e₁ ∩ pre (ᵏ ⊤) e₂ ∩ ψ [ PRDᴬ e₁ e₂ ]sᶜ
  pre ψ (FSTᴬ e) = pre (ᵏ ⊤) e ∩ ψ [ FSTᴬ e ]sᶜ
  pre ψ (SNDᴬ e) = pre (ᵏ ⊤) e ∩ ψ [ SNDᴬ e ]sᶜ
  pre _ (APPᴬ {ξ = ξ}{ψ = ψ} f e) = pre ξ e
  pre ψ (BOPᴬ o e₁ e₂)
    = pre (ᵏ ⊤) e₁ ∩ pre (ᵏ ⊤) e₂ ∩ ψ [ BOPᴬ o e₁ e₂ ]sᶜ
  pre ψ e = ψ [ e ]sᶜ  -- It's just subst for the rest

  pre⃗ {ξ = ξ}{ψ = ψ} (FUNᴬ e) = ξ ∩ pre ψ e
\end{code}}

\newcommand{\vcDef}{%
\begin{code}
  vc  : ∀{Γ}{T} → (⟦ Γ ⟧C → Set) → (⟦ Γ ▸ T ⟧C → Set)
       → Γ ⊢ᴬ T → Set
  vc⃗ : ∀{Γ}{S T}{ξ}{ψ} → (⟦ Γ ⟧C → Set)
       → Γ ⊢ᴬ S ❴ ξ ❵⟶ T ❴ ψ ❵ → Set

  vc ϕ ψ (SUᴬ e) = vc ϕ (ᵏ ⊤) e
  vc ϕ ψ (IFᴬ c e₁ e₂)
    = vc ϕ (ᵏ ⊤) c
    × vc (λ γ → ϕ γ × ⟦ c ⟧⊢ᴬ γ ≡ true) ψ e₁
    × vc (λ γ → ϕ γ × ⟦ c ⟧⊢ᴬ γ ≡ false) ψ e₂
  vc ϕ ψ (LETᴬ e₁ e₂)
    = vc ϕ (ᵏ ⊤) e₁
    × vc (λ (γ , s) → ϕ γ × s ≡ ⟦ e₁ ⟧⊢ᴬ γ)
         (λ ((γ , _) , t) → ψ (γ , t)) e₂
  vc ϕ ψ (PRDᴬ e₁ e₂) = vc ϕ (ᵏ ⊤) e₁ × vc ϕ (ᵏ ⊤) e₂
  vc ϕ ψ (FSTᴬ e) = vc ϕ (ᵏ ⊤) e
  vc ϕ ψ (SNDᴬ e) = vc ϕ (ᵏ ⊤) e
  vc {Γ} ϕ ψ′ (APPᴬ {S = S}{T = T}{ξ = ξ}{ψ = ψ} f e)
    = vc⃗ ϕ f
    × vc ϕ ξ e
    × (∀(γ : ⟦ Γ ⟧C)(s : ⟦ S ⟧τ)(t : ⟦ T ⟧τ)
      → ϕ γ → ξ (γ , s) → ψ ((γ , s) , t) → ψ′ (γ , t))
  vc ϕ ψ (BOPᴬ o e₁ e₂) = vc ϕ (ᵏ ⊤) e₁ × vc ϕ (ᵏ ⊤) e₂
  vc _ _ _ = ⊤
  
  vc⃗ {Γ = Γ}{S = S}{T = T} ϕ (FUNᴬ {ξ = ξ}{ψ = ψ} e)
    = (∀(γ : ⟦ Γ ⟧C)(s : ⟦ S ⟧τ) → ϕ γ → ξ (γ , s)
                                → pre ψ e (γ , s))
    × vc (λ (γ , s) → ϕ γ × ξ (γ , s)) ψ e
\end{code}}


\begin{figure}
\begin{minipage}{0.48\textwidth}
\begin{center}\preDef\end{center}
\end{minipage}
\caption{The Agda definition of $\pre$.}
\label{fig:pre-def}
\end{figure}

\begin{figure}
\begin{minipage}{0.48\textwidth}
\begin{center}\vcDef\end{center}
\end{minipage}
\caption{The Agda definition of $\vc$.}
\label{fig:vc-def}
\end{figure}


Unlike the development in the book of \citet{Nipkow_Klein:Isabelle}, in our language \annlang,
the definition of $\pre$ deviates from $\wpc$ by quite a long way.
For example, the typing rule for $\SUCC$ looks like:
\begin{inductive0}
\inferrule
  {Γ ; ϕ ⊢_C : \hat{e} : \RefTy{ν}{ℕ}{ξ}}
  {Γ ; ϕ ⊢_C : \SUCC\ \hat{e} : \RefTy{ν}{ℕ}{ν = \textsf{suc}\ \hat{e}}}
  {\textsf{SUᶜ}}
\end{inductive0}
Intuitively, when we run the $\wpc$ backwards on $\SUCC\ \hat{e}$ with
a postcondition $ψ$, it results in $ψ[\denotTmA{\textsf{suc}\ \hat{e}}γ/ν]$ for a semantic environement $γ$.
The inferred refinement $ξ$
of $\hat{e}$ in the premise is arbitrary and appears to be irrelevant to the
computation of the weakest precondition of the whole term. Therefore we can
set $ξ$ to be the trivial refinement ($\TT$) and there is nothing to be assumed
about the context to refine $\hat{e}$. This is however not the case in the presence of function contracts.
In general, a trivial postcondition does not entail a trivial precondition: $\pre\ ϕ\ (λ \_ .\, \TT)\ \hat{e} ≠ (λ \_.\, \TT)$.
For instance, if $\hat{e}$ is a function application, then we also need to compute the
weakest precondition for the argument to satisfy the contract.

Our $\vc$ function also differs slightly from its counterpart in the imperative setting:
it additionally takes the precondition as an argument. This is because in a purely functional
language, we do not carry over all the information in the precondition to the postcondition,
as the precondition is an invariant (recall that in the subtyping rule $\textsf{SUBᴿ}$, the entailment
is $ϕ \vDash ψ ⇒ ψ′$). 


To see it in action, we consider the following definitions again:
\begin{align*}
&f₀ᴬ = (λ x. \, x + 1) ∷ \RefTy{ν}{ℕ}{ν < 2} ⟶ \RefTy{ν}{ℕ}{ν < 4} \\
&ex₂ᴬ = (f₀ᴬ\ 1) + 2
\end{align*}
If we assign $ex₂ᴬ$ a postcondition $λ ν.\, ν < 6$, then
$\pre$ computes the weakest precondition to be $1 < 2 ∧ δ (f₀ᴬ, 1) + 2 < 6$. It checks the argument $1$
against $f₀ᴬ$'s input type, and the whole expression against the given postcondition.
The $\vc$ function validates that $f₀ᴬ$ correctly implements its specification as the type signature sets
out.

\begin{code}[hide]

  module Examples where

    private variable Γ : Cx

    ONEᴬ TWOᴬ THREEᴬ : Γ ⊢ᴬ ‵ℕ′
    ONEᴬ = SUᴬ ZEᴬ
    TWOᴬ = SUᴬ ONEᴬ
    THREEᴬ = SUᴬ TWOᴬ

    ONEᶜ : ∀{ϕ} → Γ ❴ ϕ ❵⊢ᶜ ‵ℕ′ ❴ (_≡ 1) ∘ proj₂ ❵
    ONEᶜ = SUᶜ ZEᶜ

    TWOᶜ : ∀{ϕ} → Γ ❴ ϕ ❵⊢ᶜ ‵ℕ′ ❴ (_≡ 2) ∘ proj₂ ❵
    TWOᶜ = SUᶜ ONEᶜ


    f₀ᶜ : ∀{ϕ} → Γ ❴ ϕ ❵⊢ᶜ ‵ℕ′ ❴ (_< 2) ∘ proj₂ ❵⟶ ‵ℕ′ ❴ (_< 4) ∘ proj₂ ❵
    f₀ᶜ = FUNᶜ (SUBᶜ (BOPᶜ [+] (VARᶜ top) ONEᶜ) _
               λ (γ , x) ν (_ , x<2) ν≡x+1 → subst (_< 4) (sym ν≡x+1) (+-monoˡ-< 1 (<-trans x<2 (s≤s (s≤s (s≤s {n = 0} z≤n))))))

    ex₀ᶜ : ∀{ϕ} → Γ ❴ ϕ ❵⊢ᶜ ‵ℕ′ ❴ (_< 5) ∘ proj₂ ❵
    ex₀ᶜ = SUBᶜ (APPᶜ f₀ᶜ (SUBᶜ ONEᶜ _ (λ γ ν _ ν≡1 → subst (_< 2) (sym ν≡1) (s≤s (s≤s z≤n)))))
                _ λ γ ν _ (_ , _ , ν<4) → <-trans ν<4 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

    
    f₀ᴬ : Γ ⊢ᴬ ‵ℕ′ ❴ (_< 2) ∘ proj₂ ❵⟶ ‵ℕ′ ❴ (_< 4) ∘ proj₂ ❵
    f₀ᴬ = FUNᴬ (BOPᴬ [+] (VARᴬ top) ONEᴬ)
    
    ex₀ᴬ : Γ ⊢ᴬ ‵ℕ′
    ex₀ᴬ = APPᴬ f₀ᴬ ONEᴬ

    pre-ex₀ᴬ = pre {Γ = ‵Ε′} ((_< 5) ∘ proj₂) ex₀ᴬ
    vc-ex₀ᴬ = vc {Γ = ‵Ε′} (ᵏ ⊤) ((_< 5) ∘ proj₂) ex₀ᴬ

    ex₁ᴬ : Γ ⊢ᴬ ‵ℕ′
    ex₁ᴬ = APPᴬ f₀ᴬ TWOᴬ
    
    pre-ex₁ᴬ : _
    pre-ex₁ᴬ = pre {Γ = ‵Ε′} ((_< 5) ∘ proj₂) ex₁ᴬ
    
    vc-ex₁ᴬ : _
    vc-ex₁ᴬ = vc {Γ = ‵Ε′} (ᵏ ⊤) ((_< 5) ∘ proj₂) ex₁ᴬ

    ex₂ᴬ : Γ ⊢ᴬ ‵ℕ′
    ex₂ᴬ = BOPᴬ [+] ex₀ᴬ TWOᴬ

    pre-ex₂ᴬ : (γ : ⟦ Γ ⟧C) → Set
    pre-ex₂ᴬ = pre ((_< 6) ∘ proj₂) ex₂ᴬ

    vc-ex₂ᴬ : {Γ : Cx} → Set
    vc-ex₂ᴬ {Γ} = vc {Γ} (λ _ → mkC {Γ} f₀ᴬ) ((_< 6) ∘ proj₂) ex₂ᴬ

    ex₂ᶜ-ϕ : ⟦ Γ ⟧C → Set
    ex₂ᶜ-ϕ {Γ} γ = mkC {Γ = Γ} f₀ᴬ
    {-
        λ {Γ} γ → (x : ℕ) → x < 2 → δ f₀ᴬ γ x < 4
    -}

    ex₂ᶜ : Γ ❴ ex₂ᶜ-ϕ ❵⊢ᶜ ‵ℕ′ ❴ (_< 6) ∘ proj₂ ❵
    ex₂ᶜ = SUBᶜ (BOPᶜ [+] ex₀ᶜ TWOᶜ)
                _ (λ γ ν ϕ-prf ν≡f⟨1⟩+2 → subst (_< 6) (sym ν≡f⟨1⟩+2) (+-monoˡ-< 2 (ϕ-prf 1 (s≤s (s≤s z≤n)))))
    
    ex₃ᴬ : Γ ⊢ᴬ ‵ℕ′
    ex₃ᴬ = BOPᴬ [+] ex₀ᴬ ex₂ᴬ
    
    pre-ex₃ᴬ : _
    pre-ex₃ᴬ = pre {Γ = ‵Ε′} ((_< 10) ∘ proj₂) ex₃ᴬ
    
    pre-ex₃ᴬ-prf : ex₂ᶜ-ϕ tt → pre-ex₃ᴬ tt
    pre-ex₃ᴬ-prf ϕ-prf = (tt , (s≤s (s≤s z≤n)))
                       , (((tt , (s≤s (s≤s z≤n)))
                          , (((tt , tt) , tt) , tt)) , (+-mono-< (ϕ-prf 1 (s≤s (s≤s z≤n))) (+-monoˡ-< 2 (ϕ-prf 1 (s≤s (s≤s z≤n))))))
    
    vc-ex₃ᴬ : _
    vc-ex₃ᴬ = vc {Γ = ‵Ε′} ex₂ᶜ-ϕ ((_< 10) ∘ proj₂) ex₃ᴬ
    
    vc-ex₃ᴬ-prf : vc-ex₃ᴬ
    vc-ex₃ᴬ-prf = (((λ _ s ϕ-prf s<2 → tt , (tt , tt) , (<-trans (+-monoˡ-< 1 s<2) (s≤s (s≤s (s≤s (s≤s z≤n)))))) , tt , tt)
                  , tt , (λ _ _ _ _ _ _ → tt))
                , ((((λ _ s ϕ-prf s<2 → tt , ((tt , tt) , <-trans (+-monoˡ-< 1 s<2) (s≤s (s≤s (s≤s (s≤s z≤n)))))) , (tt , tt))
                    , (tt , (λ _ _ _ _ _ _ → tt))) , tt)
\end{code}

\subsection{Meta-properties of $\pre$ and $\vc$}

We first state monotonicity lemmas of $\pre$ and $\vc$.

\begin{lemma}[$\pre$ is monotone]\label{lemma:mono-pre}
For an annotated expression $Γ ⊢_A e : T$ in \annlang, if
a predicate $ψ₁$ implies $ψ₂$, then
$\pre\ ψ₁\ e$ implies $\pre\ ψ₂\ e$.
\end{lemma}

\begin{lemma}[$\vc$ is monotone]\label{lemma:mono-vc}
For an annotated expression $Γ ⊢_A e : T$ in \annlang, if
a predicate $ϕ₂$ implies $ϕ₁$, and under the stronger precondition $ϕ₂$,
a postcondition $ψ₁$ implies $ψ₂$, 
then $\vc\ ϕ₁\ ψ₁\ e$ implies $\vc\ ϕ₂\ ψ₂\ e$.
\end{lemma}


\begin{code}[hide]
  pre-mono : ∀{Γ}{γ : ⟦ Γ ⟧C}{T}{ψ₁ ψ₂ : ⟦ Γ ▸ T ⟧C → Set}
           → (e : Γ ⊢ᴬ T)
           → ((t : ⟦ T ⟧τ) → ψ₁ (γ , t) → ψ₂ (γ , t))
           → (pre ψ₁ e γ → pre ψ₂ e γ)
  pre-mono {γ = γ} (VARᴬ x) ψ₁⇒ψ₂ = ψ₁⇒ψ₂ (⟦ x ⟧∋ γ)
  pre-mono UNITᴬ ψ₁⇒ψ₂ = ψ₁⇒ψ₂ tt
  pre-mono TTᴬ ψ₁⇒ψ₂ = ψ₁⇒ψ₂ true
  pre-mono FFᴬ ψ₁⇒ψ₂ = ψ₁⇒ψ₂ false
  pre-mono ZEᴬ ψ₁⇒ψ₂ = ψ₁⇒ψ₂ zero
  pre-mono {γ = γ} (SUᴬ e) ψ₁⇒ψ₂ (pre , ψ₁-prf) = pre , (ψ₁⇒ψ₂ (suc (⟦ e ⟧⊢ᴬ γ)) ψ₁-prf)
  pre-mono {γ = γ} (IFᴬ c e₁ e₂) ψ₁⇒ψ₂ (pre , pre′) with ⟦ c ⟧⊢ᴬ γ
  ... | true  = pre , pre-mono e₁ ψ₁⇒ψ₂ pre′
  ... | false = pre , pre-mono e₂ ψ₁⇒ψ₂ pre′
  pre-mono {γ = γ} (LETᴬ e₁ e₂) ψ₁⇒ψ₂ (pre₁ , pre₂)
    = pre₁ , (pre-mono e₂ ψ₁⇒ψ₂ pre₂)
  pre-mono {γ = γ} (PRDᴬ e₁ e₂) ψ₁⇒ψ₂ (pre₁ , pre₂ , ψ₁-prf) = pre₁ , pre₂ , (ψ₁⇒ψ₂ (⟦ e₁ ⟧⊢ᴬ γ , ⟦ e₂ ⟧⊢ᴬ γ) ψ₁-prf)
  pre-mono {γ = γ} (FSTᴬ e) ψ₁⇒ψ₂ (pre , ψ₁-prf) = pre , ψ₁⇒ψ₂ (proj₁ (⟦ e ⟧⊢ᴬ γ)) ψ₁-prf
  pre-mono {γ = γ} (SNDᴬ e) ψ₁⇒ψ₂ (pre , ψ₁-prf) = pre , ψ₁⇒ψ₂ (proj₂ (⟦ e ⟧⊢ᴬ γ)) ψ₁-prf
  pre-mono {γ = γ} (APPᴬ (FUNᴬ f) e) ψ₁⇒ψ₂ pre = pre
  pre-mono {γ = γ} (BOPᴬ o e₁ e₂) ψ₁⇒ψ₂ (pre₁ , pre₂ , ψ₁-prf) = pre₁ , pre₂ , (ψ₁⇒ψ₂ (⟦ e₁ ⟧⊢ᴬ γ ⟦ o ⟧⊢⊕ ⟦ e₂ ⟧⊢ᴬ γ) ψ₁-prf)
  
  vc-mono : ∀{Γ}{T}{ϕ₁ ϕ₂}{ψ₁ ψ₂ : ⟦ Γ ▸ T ⟧C → Set}
           → (e : Γ ⊢ᴬ T)
           → ((γ : ⟦ Γ ⟧C) → (ϕ₂ γ → ϕ₁ γ) × ((t : ⟦ T ⟧τ) → ϕ₂ γ → ψ₁ (γ , t) → ψ₂ (γ , t)))
           → (vc ϕ₁ ψ₁ e → vc ϕ₂ ψ₂ e)

  vc⃗-mono : ∀{Γ}{S T}{ϕ₁ ϕ₂}{ξ}{ψ}
            → (f : Γ ⊢ᴬ S ❴ ξ ❵⟶ T ❴ ψ ❵)
            → ((γ : ⟦ Γ ⟧C) → ϕ₂ γ → ϕ₁ γ)
            → (vc⃗ ϕ₁ f → vc⃗ ϕ₂ f)

  vc-mono (VARᴬ x) _ = ᵏ tt
  vc-mono UNITᴬ _ = ᵏ tt
  vc-mono TTᴬ _ = ᵏ tt
  vc-mono FFᴬ _ = ᵏ tt
  vc-mono ZEᴬ _ = ᵏ tt
  vc-mono (SUᴬ e) prf vc
    = vc-mono {ψ₁ = ᵏ ⊤} e (λ γ → proj₁ (prf γ) , λ _ _ → ᵏ tt) vc
  vc-mono (IFᴬ c e₁ e₂) prf (vc-c , vc₁ , vc₂)
    = vc-mono c (λ γ → proj₁ (prf γ) , λ _ _ _ → tt) vc-c
    , vc-mono e₁ (λ γ → (λ (ϕ₂-prf , c≡true) → proj₁ (prf γ) ϕ₂-prf , c≡true) , λ t → λ (ϕ₂-prf , c≡true) ψ₁-prf → (proj₂ ∘ prf) γ t ϕ₂-prf ψ₁-prf) vc₁
    , vc-mono e₂ ((λ γ → (λ (ϕ₂-prf , c≡false) → proj₁ (prf γ) ϕ₂-prf , c≡false) , λ t → λ (ϕ₂-prf , c≡false) ψ₁-prf → (proj₂ ∘ prf) γ t ϕ₂-prf ψ₁-prf)) vc₂
  vc-mono (LETᴬ {S = S} e₁ e₂) prf (vc₁ , vc₂)
    = vc-mono e₁ (λ γ → proj₁ (prf γ) , λ _ _ _ → tt) vc₁
    , vc-mono e₂ (λ (γ , s) → (λ (ϕ₂-prf , x-≡) → ((proj₁ ∘ prf) γ ϕ₂-prf) , x-≡) , λ t (ϕ₂-prf , x-≡) ψ₁-prf → (proj₂ ∘ prf) γ t ϕ₂-prf ψ₁-prf) vc₂
  vc-mono (PRDᴬ e₁ e₂) prf (vc₁ , vc₂)
    = (vc-mono e₁ (λ γ → (proj₁ (prf γ)) , (λ _ _ _ → tt)) vc₁)
    , (vc-mono e₂ (λ γ → (proj₁ (prf γ)) , (λ _ _ _ → tt)) vc₂)
  vc-mono (FSTᴬ e) prf vc
    = vc-mono {ψ₁ = ᵏ ⊤} e (λ γ → proj₁ (prf γ) , λ _ _ → ᵏ tt) vc
  vc-mono (SNDᴬ e) prf vc
    = vc-mono {ψ₁ = ᵏ ⊤} e (λ γ → proj₁ (prf γ) , λ _ _ → ᵏ tt) vc
  vc-mono (APPᴬ f e) prf (vc-f , vc-e , vc-r)
    = vc⃗-mono f (proj₁ ∘ prf) vc-f
    , vc-mono e (λ γ → proj₁ (prf γ) , λ _ _ → id) vc-e
    , λ γ s t ϕ₂-prf ψ-prf ξ-prf → (proj₂ ∘ prf) γ t ϕ₂-prf (vc-r γ s t (proj₁ (prf γ) ϕ₂-prf) ψ-prf ξ-prf)
  vc-mono (BOPᴬ o e₁ e₂) prf (vc₁ , vc₂)
    = (vc-mono e₁ (λ γ → (proj₁ (prf γ)) , (λ _ _ _ → tt)) vc₁)
    , (vc-mono e₂ (λ γ → (proj₁ (prf γ)) , (λ _ _ _ → tt)) vc₂)

  vc⃗-mono (FUNᴬ e) ϕ₂⇒ϕ₁ (p , vc-e)
    = (λ γ s ϕ₂-prf ξ-prf → p γ s (ϕ₂⇒ϕ₁ γ ϕ₂-prf) ξ-prf)
    , vc-mono e (λ (γ , s) → (λ (ϕ₂-prf , ξ-prf) → (ϕ₂⇒ϕ₁ γ ϕ₂-prf) , ξ-prf) , λ _ _ → id) vc-e
\end{code}

With the monotonicity lemmas, we can finally prove the soundness and completeness
of $\pre$ and $\vc$ with respect to the typing rules of \complang.

\begin{theorem}[Completeness of $\pre$ and $\vc$ w.r.t. \complang typing rules]
If $Γ;ϕ ⊢_C \hat{e} : \RefTy{ν}{T}{ψ}$, then $\vc\ ϕ\ ψ\ ⌜ \hat{e} ⌝ᶜ$
and $ϕ\ γ ⇒ \pre\ ψ\ ⌜ \hat{e} ⌝ᶜ\ γ$ for any semantic environment $γ$ that respects $Γ$.
\end{theorem}


\begin{code}[hide]
  pre-completeness : ∀{Γ}{T}{ϕ}{ψ}
                      → (e : Γ ❴ ϕ ❵⊢ᶜ T ❴ ψ ❵)
                      → (γ : ⟦ Γ ⟧C) → ϕ γ → pre ψ ⌜ e ⌝ᶜ γ

  pre-completeness (VARᶜ i) _ = ᵏ refl
  pre-completeness UNITᶜ _ = ᵏ refl
  pre-completeness TTᶜ _ = ᵏ refl
  pre-completeness FFᶜ _ = ᵏ refl
  pre-completeness ZEᶜ _ = ᵏ refl
  pre-completeness (SUᶜ e) γ ϕ-prf
    = (pre-mono ⌜ e ⌝ᶜ (λ _ _ → tt) (pre-completeness e γ ϕ-prf)) , refl
  pre-completeness (IFᶜ c e₁ e₂) γ ϕ-prf
    with ⟦ ⌜ c ⌝ᶜ ⟧⊢ᴬ γ in cond
  ... | true  = pre-mono ⌜ c ⌝ᶜ (λ _ _ → tt) (pre-completeness c γ ϕ-prf)
              , pre-completeness e₁ γ (ϕ-prf , cond)
  ... | false = pre-mono ⌜ c ⌝ᶜ (λ _ _ → tt) (pre-completeness c γ ϕ-prf)
              , pre-completeness e₂ γ (ϕ-prf , cond)
  pre-completeness (LETᶜ e₁ e₂) γ ϕ-prf
    = (pre-mono ⌜ e₁ ⌝ᶜ (λ _ _ → tt) (pre-completeness e₁ γ ϕ-prf))
    , (pre-completeness e₂ (γ , ⟦ ⌜ e₁ ⌝ᶜ ⟧⊢ᴬ γ) (ϕ-prf , refl))
  pre-completeness (PRDᶜ e₁ e₂) γ ϕ-prf
    = pre-mono ⌜ e₁ ⌝ᶜ (λ _ _ → tt) (pre-completeness e₁ γ ϕ-prf)
    , pre-mono ⌜ e₂ ⌝ᶜ (λ _ _ → tt) (pre-completeness e₂ γ ϕ-prf)
    , refl
  pre-completeness (FSTᶜ e) γ ϕ-prf
    = pre-mono ⌜ e ⌝ᶜ (λ _ _ → tt) (pre-completeness e γ ϕ-prf) , refl
  pre-completeness (SNDᶜ e) γ ϕ-prf
    = pre-mono ⌜ e ⌝ᶜ (λ _ _ → tt) (pre-completeness e γ ϕ-prf) , refl
  pre-completeness (APPᶜ f e) = pre-completeness e
  pre-completeness (BOPᶜ o e₁ e₂) γ ϕ-prf
    = pre-mono ⌜ e₁ ⌝ᶜ (λ _ _ → tt) (pre-completeness e₁ γ ϕ-prf)
    , pre-mono ⌜ e₂ ⌝ᶜ (λ _ _ → tt) (pre-completeness e₂ γ ϕ-prf)
    , refl
  pre-completeness {ϕ = ϕ}{ψ = ψ} (SUBᶜ {ψ = ψ′} e _ sub) γ ϕ-prf
    = pre-mono ⌜ e ⌝ᶜ (λ t → sub γ t ϕ-prf) (pre-completeness e γ ϕ-prf)


  vc-completeness : ∀{Γ}{T}{ϕ}{ψ}
                  → (e : Γ ❴ ϕ ❵⊢ᶜ T ❴ ψ ❵)
                  → vc ϕ ψ ⌜ e ⌝ᶜ
  vc⃗-completeness : ∀{Γ}{S T}{ϕ}{ξ}{ψ}
                   → (f : Γ ❴ ϕ ❵⊢ᶜ S ❴ ξ ❵⟶ T ❴ ψ ❵)
                   → vc⃗ ϕ ⌜ f ⌝ᶜ⃗

  vc-completeness (VARᶜ i) = tt
  vc-completeness UNITᶜ = tt
  vc-completeness TTᶜ = tt
  vc-completeness FFᶜ = tt
  vc-completeness ZEᶜ = tt
  vc-completeness (SUᶜ e) = vc-mono ⌜ e ⌝ᶜ (λ γ → id , λ _ _ _ → tt) (vc-completeness e)
  vc-completeness (IFᶜ c e₁ e₂)
    = vc-mono ⌜ c ⌝ᶜ (λ _ → id , λ _ _ _ → tt) (vc-completeness c)
    , vc-completeness e₁
    , vc-completeness e₂
  vc-completeness (LETᶜ {ϕ = ϕ}{ξ = ξ}{ψ = ψ} e₁ e₂)
    = (vc-mono ⌜ e₁ ⌝ᶜ (λ _ → id , λ _ _ _ → tt) (vc-completeness e₁))
    , (vc-mono ⌜ e₂ ⌝ᶜ (λ γ → id , λ _ _ → id) (vc-completeness e₂))
  vc-completeness (PRDᶜ e₁ e₂)
    = vc-mono ⌜ e₁ ⌝ᶜ (λ _ → id , λ _ _ _ → tt) (vc-completeness e₁)
    , vc-mono ⌜ e₂ ⌝ᶜ (λ _ → id , λ _ _ _ → tt) (vc-completeness e₂)
  vc-completeness (FSTᶜ e)
    = vc-mono ⌜ e ⌝ᶜ (λ _ → id , λ _ _ _ → tt) (vc-completeness e)
  vc-completeness (SNDᶜ e)
    = vc-mono ⌜ e ⌝ᶜ (λ _ → id , λ _ _ _ → tt) (vc-completeness e)
  vc-completeness (APPᶜ f e)
    = vc⃗-completeness f
    , vc-completeness e
    , λ γ s t ϕ-prf ξ-prf ψ-prf → s , ξ-prf , ψ-prf
  vc-completeness (BOPᶜ o e₁ e₂)
    = vc-mono ⌜ e₁ ⌝ᶜ (λ _ → id , λ _ _ _ → tt) (vc-completeness e₁)
    , vc-mono ⌜ e₂ ⌝ᶜ (λ _ → id , λ _ _ _ → tt) (vc-completeness e₂)
  vc-completeness (SUBᶜ e _ sub)
    = vc-mono ⌜ e ⌝ᶜ (λ γ → id , (sub γ)) (vc-completeness e)

  vc⃗-completeness (FUNᶜ e)
    = (λ γ s ϕ-prf ξ-prf → pre-completeness e (γ , s) (ϕ-prf , ξ-prf))
    , vc-completeness e
\end{code}


\begin{corollary}\label{cor:prevc-sound}
For an expression $Γ ⊢_A e : T$ in \annlang , if $\vc\ ϕ\ ψ\ e$
and $ϕ\ γ ⇒ \pre\ ψ\ e\ γ$ for any semantic environment $γ$ that respects $Γ$, then
there is a type derivation $Γ;ϕ ⊢_C \hat{e} : \RefTy{ν}{T}{ψ}$ such that $⌜ \hat{e} ⌝ᶜ = e$.
\end{corollary}


\begin{theorem}[Soundness of $\pre$ and $\vc$ w.r.t. \complang typing rules]
For an expression $Γ ⊢_A e : T$ in \annlang, if $\vc\ (\pre\ ψ\ e)\ ψ\ e$, then
there is a type derivation $Γ;\pre\ ψ\ e ⊢_C \hat{e} : \RefTy{ν}{T}{ψ}$ such that $⌜ \hat{e} ⌝ᶜ = e$.
\end{theorem}



\begin{code}[hide]
  prevc-soundness′ : ∀{Γ}{T}{ϕ}{ψ}
                   → (e : Γ ⊢ᴬ T)
                   → vc ϕ ψ e
                   → (∀(γ : ⟦ Γ ⟧C) → ϕ γ → pre ψ e γ)
                   → Σ (Γ ❴ ϕ ❵⊢ᶜ T ❴ ψ ❵) λ e′ → ⌜ e′ ⌝ᶜ ≡ e

  prevc-soundness′ {ψ = ψ} (VARᴬ x) vc p
    = SUBᶜ (VARᶜ x) _ (λ γ _ ϕ-prf ν-≡ → subst (˄ ψ γ) (sym ν-≡) (p γ ϕ-prf)) , refl
  prevc-soundness′ {ψ = ψ} UNITᴬ vc p
    = SUBᶜ UNITᶜ ψ (λ γ _ ϕ-prf ν-≡ → subst (˄ ψ γ) (sym ν-≡) (p γ ϕ-prf)) , refl
  prevc-soundness′ {ψ = ψ} TTᴬ vc p
    = SUBᶜ TTᶜ ψ (λ γ _ ϕ-prf ν-≡ → subst (˄ ψ γ) (sym ν-≡) (p γ ϕ-prf)) , refl
  prevc-soundness′ {ψ = ψ} FFᴬ vc p
    = SUBᶜ FFᶜ ψ (λ γ _ ϕ-prf ν-≡ → subst (˄ ψ γ) (sym ν-≡) (p γ ϕ-prf)) , refl
  prevc-soundness′ {ψ = ψ} ZEᴬ vc p
    = SUBᶜ ZEᶜ ψ (λ γ _ ϕ-prf ν-≡ → subst (˄ ψ γ) (sym ν-≡) (p γ ϕ-prf)) , refl
  prevc-soundness′ {ψ = ψ} (SUᴬ e) vc p
    with e′ , e-≡ ← prevc-soundness′ e vc (λ γ ϕ-prf → proj₁ (p γ ϕ-prf))
    rewrite sym e-≡
    = (SUBᶜ (SUᶜ e′) ψ (λ γ _ ϕ-prf ν-≡ → subst (˄ ψ γ) (sym ν-≡) ((proj₂ (p γ ϕ-prf))))) , refl
  prevc-soundness′ (IFᴬ c e₁ e₂) (vc-c , vc₁ , vc₂) p
    with c′ , c-≡ ← prevc-soundness′ c vc-c (λ γ ϕ-prf → proj₁ (p γ ϕ-prf)) |
         e₁′ , e₁-≡ ← prevc-soundness′ e₁ vc₁ (λ γ (ϕ-prf , c≡true) → subst (λ x → if x then _ else _) c≡true (proj₂ (p γ ϕ-prf))) |
         e₂′ , e₂-≡ ← prevc-soundness′ e₂ vc₂ (λ γ (ϕ-prf , c≡false) → subst (λ x → if x then _ else _) c≡false (proj₂ (p γ ϕ-prf)))
    rewrite sym c-≡ | sym e₁-≡ | sym e₂-≡
    = (IFᶜ c′ e₁′ e₂′) , refl 
  prevc-soundness′ {ψ = ψ} (LETᴬ e₁ e₂) (vc₁ , vc₂) p
    with e₁′ , e₁-≡ ← prevc-soundness′ e₁ vc₁ (λ γ ϕ-prf → proj₁ (p γ ϕ-prf)) |
         e₂′ , e₂-≡ ← prevc-soundness′ e₂ vc₂ (λ (γ , s) (ϕ-prf , x-≡) → subst (λ x → pre (λ γ @ (((a , _) , b)) → ψ (a , b)) e₂ (γ , x)) (sym x-≡) (proj₂ (p γ ϕ-prf)))
    rewrite sym e₁-≡ | sym e₂-≡
    = LETᶜ e₁′ e₂′ , refl
  prevc-soundness′ {ψ = ψ} (PRDᴬ e₁ e₂) (vc₁ , vc₂) p
    with e₁′ , e₁-≡ ← prevc-soundness′ e₁ vc₁ (λ γ ϕ-prf → proj₁ (p γ ϕ-prf)) |
         e₂′ , e₂-≡ ← prevc-soundness′ e₂ vc₂ (λ γ ϕ-prf → proj₁ (proj₂ (p γ ϕ-prf)))
    rewrite sym e₁-≡ | sym e₂-≡
    = SUBᶜ (PRDᶜ e₁′ e₂′) ψ (λ γ x,y ϕ-prf ν-≡ → subst (˄ ψ γ) (sym ν-≡) (proj₂ (proj₂ (p γ ϕ-prf)))) , refl
  prevc-soundness′ {ψ = ψ} (FSTᴬ e) vc p
    with e′ , e-≡ ← prevc-soundness′ e vc (λ γ ϕ-prf → proj₁ (p γ ϕ-prf))
    rewrite sym e-≡
    = (SUBᶜ (FSTᶜ e′) ψ (λ γ _ ϕ-prf ν-≡ → subst (˄ ψ γ) (sym ν-≡) (proj₂ (p γ ϕ-prf)))) , refl
  prevc-soundness′ {ψ = ψ} (SNDᴬ e) vc p
    with e′ , e-≡ ← prevc-soundness′ e vc (λ γ ϕ-prf → proj₁ (p γ ϕ-prf))
    rewrite sym e-≡
    =  (SUBᶜ (SNDᶜ e′) ψ (λ γ _ ϕ-prf ν-≡ → subst (˄ ψ γ) (sym ν-≡) (proj₂ (p γ ϕ-prf)))) , refl
  prevc-soundness′ {ψ = ψ} (APPᴬ (FUNᴬ f) e) (vc-f , vc-e , vc-r) p
    with f′ , f-≡ ← prevc-soundness′ f (proj₂ vc-f) (λ (γ , s) (ϕ-prf , ξ-prf) → proj₁ vc-f γ s ϕ-prf ξ-prf) |
         e′ , e-≡ ← prevc-soundness′ e vc-e p
    rewrite sym f-≡ | sym e-≡ 
    = SUBᶜ (APPᶜ (FUNᶜ f′) e′) ψ (λ γ t ϕ-prf (s , ξ-prf , ψ₁-prf) → vc-r γ s t ϕ-prf ξ-prf ψ₁-prf)
    , refl
  prevc-soundness′ {ψ = ψ} (BOPᴬ o e₁ e₂) (vc₁ , vc₂) p
    with e₁′ , e₁-≡ ← prevc-soundness′ e₁ vc₁ (λ γ ϕ-prf → proj₁ (p γ ϕ-prf)) |
         e₂′ , e₂-≡ ← prevc-soundness′ e₂ vc₂ (λ γ ϕ-prf → proj₁ (proj₂ (p γ ϕ-prf)))
    rewrite sym e₁-≡ | sym e₂-≡
   = SUBᶜ (BOPᶜ o e₁′ e₂′) ψ (λ γ x,y ϕ-prf ν-≡ → subst (˄ ψ γ) (sym ν-≡) (proj₂ (proj₂ (p γ ϕ-prf)))) , refl

  prevc-soundness : ∀{Γ}{T}
                  → (ψ : ⟦ Γ ▸ T ⟧C → Set)
                  → (e : Γ ⊢ᴬ T)
                  → (vc (pre ψ e) ψ e)
                  → Σ (Γ ❴ pre ψ e ❵⊢ᶜ T ❴ ψ ❵) λ e′ → ⌜ e′ ⌝ᶜ ≡ e
  prevc-soundness ψ e vc = prevc-soundness′ e vc λ _ → id
\end{code}   



\section{Related Work, Future Work and Conclusion}

There is a very long line of prior work on refinement types, e.g.\ 
\citep{Rondon_KJ_08, Vazou:phd, Knowles_Flanagan_09, Lehmann_Tanter_17, Pavlinovic_SW_21}, just to name a few.
We find the work by \citet{Lehmann_Tanter_16} most comparable. They define the language and the logical
formulae fully deeply in Coq, and assumes an oracle that can answer the questions about logical entailment.
In our formalisation, we interpret the language as shallow Agda terms, and the underlying logic
is Agda's type system. Programmers serve as an oracle to construct proof terms.
\citet{Knowles_Flanagan_07}'s work is also closely related. It develops a decidable type reconstruction
algorithm which preserves the typeability of a program. Their type reconstruction is highly influenced by
the strongest postcondition predicate transformation.

\vspace{1em}
Admittedly, our attempt in formalising refinement type systems is still in its infancy.
We list a few directions for future exploration.

\paragraph{Language features}
The languages that we presented in this paper are very preliminary. They do
not yet support higher-order functions. Variants of Hoare style logics that deal with higher-order
language features~\citep{Jung_KJBBD_18, Yoshida_HB_07, Regis-Gianas_Pottier_08, Schwinghammer_BRBY_09, Charlton_11} will shed light on the extension to higher-order functions.
It remains to be seen
which techniques are compatible with the way in which the language
is embedded and interpreted in Agda.
General recursion is also missing from our formalisation. We surmise
that recursion can be handled analogously to how a \textsf{WHILE}-loop is
dealt with in Hoare logic.
Hoare logic style reasoning turns out to be instrumental in languages with
side-effects or concurrency.
How to extend the unifying paradigm to languages with such features is
also an open question. An equivalent question is how to formulate
proof systems that support these features in terms of refinement type systems.


\paragraph{Delaying proof obligations}
As we have seen
in the examples, constructing a typing tree for a program requires the developer to fill the holes
with proof terms. The typechecking algorithm with $\pre$ and $\vc$ collects the proof obligations along the typing tree. 
This is effectively deferring the proofs to a later stage. It shares the same spirit as the \textsf{Delay}
applicative functor by \citet{OConnor_19}. It is yet to be seen how it can be applied in the construction
of the typing trees in our formalisation.

\paragraph{Compositionality}
We stated in \autoref{sec:comp-lang} that the \complang language is not yet fully compositional
in the sense of \citep{Knowles_Flanagan_09}. The interpretation function $\denotTmA{\cdot}$ is used in the definition
of $\pre$, and that effectively leaks the behaviour of the program to the reasoning thereof,
penetrating the layer of abstraction provided by types.
We dealt with it for functions: the
implementation details of the function body and those of
the argument are hidden from the reasoning process. We would like
to further extend the compositional reasoning to other language constructs
(via user type annotations) in future work.

\paragraph{Other program logics}
Lastly, in our formalisation, we use Hoare logic as the foundation for the
typing rules. There are
other flavours of program logics, most notably the dual of Hoare logic---%
Reverse Hoare Logic~\citep{deVries_11} and Incorrectness Logic~\citep{O'Hearn_19}.
We are intrigued to see if we can mount these logics onto our system, and how it interacts with
a functional language that is, say, impure or concurrent.

\vspace{1em}

In this paper, we presented a simple yet novel Agda formalisation of refinement types
on a small first-order functional language in the style of Hoare logic.
It provides a testbed for studying the formal connections between refinement types
and Hoare logic.
We believe that our work is a valuable addition to the formal
investigation into refinement types, and we hope
that this work will foster more research into machine-checked formalisations
of refinement type systems,
and the connection with other logical systems such as Hoare style logics.
