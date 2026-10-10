import OAI.ModelTheory.Choiceless.Observers

namespace OAI

namespace CPTSeparation.FullCPT

noncomputable section

open Classical Hereditary Finset

open Operational (State Control)

attribute [local instance] CPTSeparation.FullCPT.instDecidableEqHF_1

variable {A R F : Type} {arity : F → ℕ}

namespace Term

variable [finiteA : Fintype A]

omit A in
@[simp] lemma elements_zero
    {A : Type}
    [Fintype A] : elements (Hereditary.ordinal (A := A) 0) = ∅ := by simp [Hereditary.ordinal]

def pack (t : Term R F arity) : Term R F arity := .pair t t

def merge (a b : Term R F arity) : Term R F arity := .union (.pair a b)

def merges (ts : List (Term R F arity)) : Term R F arity := ts.foldr merge (.ordinal 0)

def collect : Term R F arity → Term R F arity
  | t@(.var _) | t@(.ordinal _) | t@(.atoms) => pack t
  | t@(.app _ args) => merge (pack t) (merges (List.ofFn (fun i => collect (args i))))
  | t@(.pair a b) | t@(.equal a b) | t@(.member a b)
  | t@(.input _ a b) | t@(.and a b) | t@(.or a b) =>
      merge (pack t) (merge (collect a) (collect b))
  | t@(.union a) | t@(.unique a) | t@(.card a)
  | t@(.isAtom a) | t@(.not a) => merge (pack t) (collect a)
  | .conditional c a b => merge (collect c) (.conditional c (collect a) (collect b))
  | t@(.comprehend n bound guard body) => merge (pack t)
      (merge (collect bound) (.union (.comprehend n bound (.ordinal 1)
        (merge (collect guard) (.conditional guard (collect body) (.ordinal 0))))))

@[simp] lemma eval_pack (rel : R → A → A → Bool) (s : State F arity A) (t : Term R F arity) (v : ℕ → HF A) :
 (pack t).eval rel s v = ofFinset {t.eval rel s v} := by simp [pack,eval,double]

@[simp] lemma eval_merge (rel : R → A → A → Bool) (s : State F arity A) (a b : Term R F arity) (v : ℕ → HF A) :
 (merge a b).eval rel s v = ofFinset (elements (a.eval rel s v) ∪ elements (b.eval rel s v)) := by
 simp [merge,eval,Operational.unionHF,double]

@[simp] lemma eval_merges (rel : R → A → A → Bool) (s : State F arity A) (ts : List (Term R F arity)) (v : ℕ → HF A) :
 (merges ts).eval rel s v = ofFinset ((ts.map (fun t => elements (t.eval rel s v))).foldr (· ∪ ·) ∅) := by
 induction ts with
 | nil => rfl
 | cons t ts ih =>
   simp only [merges] at ih ⊢
   simp only [List.foldr_cons,eval_merge,ih,elements_ofFinset,List.map_cons,List.foldr_cons]

lemma eval_collect (rel : R → A → A → Bool) (s : State F arity A) (t : Term R F arity) (v : ℕ → HF A) :
 t.collect.eval rel s v = ofFinset (t.roots rel s v) := by
 induction t generalizing v with
 | var n => simp only [collect,roots,eval_pack]
 | ordinal n => simp only [collect,roots,eval_pack]
 | atoms => simp only [collect,roots,eval_pack]
 | app f args ih => simp only [collect,roots,eval_merge,eval_pack,eval_merges,List.map_ofFn,Function.comp_def,ih,elements_ofFinset,singleton_union]
 | pair a b iha ihb | equal a b iha ihb | member a b iha ihb
 | input r a b iha ihb | and a b iha ihb | or a b iha ihb =>
   simp only [collect,roots,eval_merge,eval_pack,iha,ihb,elements_ofFinset,singleton_union]
 | union a ih | unique a ih | card a ih | isAtom a ih | not a ih =>
   simp only [collect,roots,eval_merge,eval_pack,ih,elements_ofFinset,singleton_union]
 | conditional c a b ihc iha ihb =>
   simp only [collect,roots,eval_merge,eval,ihc,iha,ihb,elements_ofFinset]
   split <;> simp only [elements_ofFinset]
 | comprehend n bound guard body ihbound ihguard ihbody =>
   simp only [collect,roots,eval_merge,eval_pack,eval,ihbound,ihguard,ihbody,elements_ofFinset,singleton_union]
   congr 2
   simp only [Operational.unionHF,elements_ofFinset]
   congr 1
   simp only [Finset.filter_true,image_biUnion,elements_ofFinset]
   apply biUnion_congr rfl
   intro x hx
   split <;> simp [elements_ofFinset,elements_zero]

@[simp] lemma eval_spread (rel : R → A → A → Bool) (s : State F arity A)
 (n : ℕ) (bound body : Term R F arity) (v : ℕ → HF A) :
 (Term.union (Term.comprehend n bound (.ordinal 1) body)).eval rel s v =
   ofFinset ((elements (bound.eval rel s v)).biUnion
     (fun x => elements (body.eval rel s (Function.update v n x)))) := by
 simp [eval,Operational.unionHF,image_biUnion]

end Term

namespace Rule

variable [Fintype A]

def collect : Rule R F arity → Term R F arity
 | .skip => .ordinal 0
 | .update _ args value => Term.merge value.collect (Term.merges (List.ofFn (fun i => (args i).collect)))
 | .parallel a b => Term.merge (collect a) (collect b)
 | .conditional c a b => Term.merge c.collect (.conditional c (collect a) (collect b))
 | .forall n bound body => Term.merge bound.collect (.union (.comprehend n bound (.ordinal 1) (collect body)))
 | .letValue n value body => Term.merge value.collect
     (.union (.comprehend n (Term.pack value) (.ordinal 1) (collect body)))

lemma eval_collect (rel : R → A → A → Bool) (s : State F arity A) (r : Rule R F arity) (v : ℕ → HF A) :
 r.collect.eval rel s v = ofFinset (r.roots rel s v) := by
 induction r generalizing v with
 | skip => rfl
 | update f args value =>
   simp only [collect,roots,Term.eval_merge,Term.eval_merges,List.map_ofFn,Function.comp_def,Term.eval_collect,elements_ofFinset]
 | parallel a b iha ihb => simp only [collect,roots,Term.eval_merge,iha,ihb,elements_ofFinset]
 | conditional c a b iha ihb =>
   simp only [collect,roots,Term.eval_merge,Term.eval,Term.eval_collect,iha,ihb,elements_ofFinset]
   split <;> simp only [elements_ofFinset]
 | «forall» n bound body ih =>
   simp only [collect,roots,Term.eval_merge,Term.eval_spread,Term.eval_collect,ih,elements_ofFinset]
 | letValue n value body ih =>
   simp only [collect,roots,Term.eval_merge,Term.eval_spread,Term.eval_pack,Term.eval_collect,ih,elements_ofFinset,singleton_biUnion]

end Rule

namespace Program

variable (P : Program R) [Fintype A]

def rootObserver : P.compile.Observer :=
 (Term.conditional (.app (.inl .halt) Fin.elim0) (.ordinal 0) P.body.collect).compile (fun _ => none)

lemma rootObserver_eval (rel : R → A → A → Bool) (s : P.Store (A := A)) :
 P.rootObserver.eval rel s Fin.elim0 = ofFinset (P.stepRoots rel s) := by
 rw [rootObserver,Term.eval_compile rel s _ _ (fun _ => Operational.empty) Fin.elim0 (fun _ => rfl)]
 simp only [Term.eval,Rule.eval_collect,stepRoots,flag]
 have he : (fun i : Fin (P.functionArity (.inl Control.halt)) =>
     Term.eval rel s (Fin.elim0 i) (fun _ => Operational.empty)) = Fin.elim0 := by
   funext i
   exact Fin.elim0 i
 rw [he]
 split <;> simp_all only [ite_true,ite_false] ; rfl

lemma observed_compile (rel : R → A → A → Bool) (h : ℕ) :
 P.compile.observed P.rootObserver rel h = P.occurring rel h := by
 simp only [Operational.Machine.observed,occurring,P.active_compile,P.run_compile]
 congr 1
 apply biUnion_congr rfl
 intro j hj
 cases P.run rel j with
 | none => rfl
 | some s =>
   exact congrArg familyClosure ((congrArg elements (P.rootObserver_eval rel s)).trans (elements_ofFinset _))

lemma evaluationAccepts_compile (time space : Polynomial ℕ) (rel : R → A → A → Bool) :
 P.compile.polynomialObservedAccepts P.rootObserver time space rel ↔ P.evaluationAccepts time space rel := by
 simp only [Operational.Machine.polynomialObservedAccepts,Operational.Machine.observedAccepts,
   evaluationAccepts,P.run_compile,P.observed_compile,Operational.Machine.flag,flag]
 rfl

end Program

theorem query_not_evaluationDefinable : ¬ EvaluationDefinable (fun {_} [_] I => I.query) := by
 rintro ⟨P,time,space,h⟩
 apply query_not_polynomial_observed_HF
 refine ⟨P.compile,P.rootObserver,time,space,?_⟩
 intro A inst I
 exact (P.evaluationAccepts_compile time space I.rel).trans (h A I)

end

end CPTSeparation.FullCPT

end OAI
