import OAI.Computability.WitnessedChoice.LowerBound

namespace OAI


namespace WitnessedSeparation.FullCPT

noncomputable section

open Classical Hereditary Finset

open Operational (State Control Location Update)

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

inductive Term (R F : Type) (arity : F → ℕ) : Type
  | var (name : ℕ)
  | ordinal (n : ℕ)
  | atoms
  | app (f : F) (args : Fin (arity f) → Term R F arity)
  | pair (a b : Term R F arity)
  | union (a : Term R F arity)
  | unique (a : Term R F arity)
  | card (a : Term R F arity)
  | equal (a b : Term R F arity)
  | member (a b : Term R F arity)
  | isAtom (a : Term R F arity)
  | input (r : R) (a b : Term R F arity)
  | not (a : Term R F arity)
  | and (a b : Term R F arity)
  | or (a b : Term R F arity)
  | conditional (c a b : Term R F arity)
  | comprehend (name : ℕ) (bound guard body : Term R F arity)

variable {A R F : Type} {arity : F → ℕ}

namespace Term

variable [Fintype A]

def eval (rel : R → A → A → Bool) (s : State F arity A) :
    Term R F arity → (ℕ → HF A) → HF A
  | .var n, v => v n
  | .ordinal n, _ => Hereditary.ordinal n
  | .atoms, _ => Operational.allAtoms
  | .app f args, v => s.value ⟨f, fun i => eval rel s (args i) v⟩
  | .pair a b, v => double (eval rel s a v) (eval rel s b v)
  | .union a, v => Operational.unionHF (eval rel s a v)
  | .unique a, v => Operational.uniqueHF (eval rel s a v)
  | .card a, v => Operational.cardinalityHF (eval rel s a v)
  | .equal a b, v => Operational.boolean (eval rel s a v = eval rel s b v)
  | .member a b, v => Operational.boolean (eval rel s a v ∈ eval rel s b v)
  | .isAtom a, v => Operational.boolean (isSet (eval rel s a v) = false)
  | .input r a b, v => Operational.boolean (Operational.inputRelation rel r (eval rel s a v) (eval rel s b v))
  | .not a, v => Operational.boolean (eval rel s a v ≠ Operational.truth)
  | .and a b, v => Operational.boolean (eval rel s a v = Operational.truth ∧ eval rel s b v = Operational.truth)
  | .or a b, v => Operational.boolean (eval rel s a v = Operational.truth ∨ eval rel s b v = Operational.truth)
  | .conditional c a b, v => if eval rel s c v = Operational.truth then eval rel s a v else eval rel s b v
  | .comprehend n bound guard body, v =>
      ofFinset (((elements (eval rel s bound v)).filter
        (fun x => eval rel s guard (Function.update v n x) = Operational.truth)).image
        (fun x => eval rel s body (Function.update v n x)))

end Term

def bindSlots {k : ℕ} (slots : ℕ → Option (Fin k)) (name : ℕ) : ℕ → Option (Fin (k+1)) :=
  fun x => if x = name then some 0 else (slots x).map Fin.succ

def Agrees {k : ℕ} (slots : ℕ → Option (Fin k)) (env : ℕ → HF A)
    (values : Fin k → HF A) : Prop :=
  ∀ x, env x = (slots x).elim Operational.empty values

lemma agrees_bind {k : ℕ} {slots : ℕ → Option (Fin k)} {env : ℕ → HF A}
    {values : Fin k → HF A} (h : Agrees slots env values) (name : ℕ) (x : HF A) :
    Agrees (bindSlots slots name) (Function.update env name x) (Fin.cons x values) := by
  intro y
  by_cases he : y = name
  · subst y
    simp [bindSlots]
  · rw [Function.update_of_ne he]
    rw [h y]
    simp only [bindSlots, ite_eq_right he]
    cases slots y <;> rfl

namespace Term

def compile : Term R F arity → {k : ℕ} → (ℕ → Option (Fin k)) → Operational.Term R F arity k
  | .var n, _, slots => match slots n with
      | none => .constant 0
      | some i => .var i
  | .ordinal n, _, _ => .constant n
  | .atoms, _, _ => .atoms
  | .app f args, _, slots => .app f (fun i => compile (args i) slots)
  | .pair a b, _, slots => .pair (compile a slots) (compile b slots)
  | .union a, _, slots => .union (compile a slots)
  | .unique a, _, slots => .unique (compile a slots)
  | .card a, _, slots => .card (compile a slots)
  | .equal a b, _, slots => .equal (compile a slots) (compile b slots)
  | .member a b, _, slots => .member (compile a slots) (compile b slots)
  | .isAtom a, _, slots => .isAtom (compile a slots)
  | .input r a b, _, slots => .input r (compile a slots) (compile b slots)
  | .not a, _, slots => .not (compile a slots)
  | .and a b, _, slots => .and (compile a slots) (compile b slots)
  | .or a b, _, slots => .not (.and (.not (compile a slots)) (.not (compile b slots)))
  | .conditional c a b, _, slots => .conditional (compile c slots) (compile a slots) (compile b slots)
  | .comprehend n bound guard body, _, slots =>
      .comprehension (compile bound slots) (compile guard (bindSlots slots n))
        (compile body (bindSlots slots n))

theorem eval_compile [Fintype A] (rel : R → A → A → Bool) (s : State F arity A)
    (t : Term R F arity) {k : ℕ} (slots : ℕ → Option (Fin k))
    (env : ℕ → HF A) (values : Fin k → HF A) (h : Agrees slots env values) :
    (t.compile slots).eval rel s values = t.eval rel s env := by
  induction t generalizing k env with
  | var n =>
      simp only [compile, eval]
      rw [h n]
      cases slots n <;> rfl
  | ordinal n => rfl
  | atoms => rfl
  | app f args ih =>
      simp only [compile, Operational.Term.eval, eval]
      congr 2
      funext i
      exact ih i slots env values h
  | pair a b iha ihb => simp only [compile, Operational.Term.eval, eval, iha slots env values h, ihb slots env values h]
  | union a ih => simp only [compile, Operational.Term.eval, eval, ih slots env values h]
  | unique a ih => simp only [compile, Operational.Term.eval, eval, ih slots env values h]
  | card a ih => simp only [compile, Operational.Term.eval, eval, ih slots env values h]
  | equal a b iha ihb => simp only [compile, Operational.Term.eval, eval, iha slots env values h, ihb slots env values h]
  | member a b iha ihb => simp only [compile, Operational.Term.eval, eval, iha slots env values h, ihb slots env values h]
  | isAtom a ih => simp only [compile, Operational.Term.eval, eval, ih slots env values h]
  | input r a b iha ihb => simp only [compile, Operational.Term.eval, eval, iha slots env values h, ihb slots env values h]
  | not a ih => simp only [compile, Operational.Term.eval, eval, ih slots env values h]
  | and a b iha ihb => simp only [compile, Operational.Term.eval, eval, iha slots env values h, ihb slots env values h]
  | or a b iha ihb =>
      simp only [compile, Operational.Term.eval, eval, iha slots env values h, ihb slots env values h]
      simp only [ne_eq, Operational.boolean_truth, not_and_or, not_not]
  | conditional c a b ihc iha ihb =>
      simp only [compile, Operational.Term.eval, eval, ihc slots env values h, iha slots env values h, ihb slots env values h]
  | comprehend n bound guard body ihbound ihguard ihbody =>
      simp only [compile, Operational.Term.eval, eval, ihbound slots env values h]
      have hg : (fun x => Operational.Term.eval rel s (guard.compile (bindSlots slots n)) (Fin.cons x values)) =
          (fun x => eval rel s guard (Function.update env n x)) := by
        funext x
        exact ihguard _ _ _ (agrees_bind h n x)
      have hb : (fun x => Operational.Term.eval rel s (body.compile (bindSlots slots n)) (Fin.cons x values)) =
          (fun x => eval rel s body (Function.update env n x)) := by
        funext x
        exact ihbody _ _ _ (agrees_bind h n x)
      have hg' (x : HF A) := congrFun hg x
      simp only [hg', hb]

end Term

inductive Rule (R F : Type) (arity : F → ℕ) : Type
  | skip
  | update (f : F) (args : Fin (arity f) → Term R F arity) (value : Term R F arity)
  | parallel (a b : Rule R F arity)
  | conditional (condition : Term R F arity) (a b : Rule R F arity)
  | forall (name : ℕ) (bound : Term R F arity) (body : Rule R F arity)
  | letValue (name : ℕ) (value : Term R F arity) (body : Rule R F arity)

namespace Rule

def updates [Fintype A] (rel : R → A → A → Bool) (s : State F arity A) :
    Rule R F arity → (ℕ → HF A) → Finset (Update F arity A)
  | .skip, _ => ∅
  | .update f args value, v => {(⟨f, fun i => (args i).eval rel s v⟩, value.eval rel s v)}
  | .parallel a b, v => updates rel s a v ∪ updates rel s b v
  | .conditional c a b, v => if c.eval rel s v = Operational.truth then updates rel s a v else updates rel s b v
  | .forall n bound body, v => (elements (bound.eval rel s v)).biUnion
      (fun x => updates rel s body (Function.update v n x))
  | .letValue n value body, v => updates rel s body (Function.update v n (value.eval rel s v))

def compile : Rule R F arity → {k : ℕ} → (ℕ → Option (Fin k)) → Operational.Rule R F arity k
  | .skip, _, _ => .skip
  | .update f args value, _, slots => .update f (fun i => (args i).compile slots) (value.compile slots)
  | .parallel a b, _, slots => .parallel (compile a slots) (compile b slots)
  | .conditional c a b, _, slots => .conditional (c.compile slots) (compile a slots) (compile b slots)
  | .forall n bound body, _, slots => .forall (bound.compile slots) (compile body (bindSlots slots n))
  | .letValue n value body, _, slots => .letValue (value.compile slots) (compile body (bindSlots slots n))

theorem updates_compile [Fintype A] (rel : R → A → A → Bool) (s : State F arity A)
    (r : Rule R F arity) {k : ℕ} (slots : ℕ → Option (Fin k))
    (env : ℕ → HF A) (values : Fin k → HF A) (h : Agrees slots env values) :
    (r.compile slots).updates rel s values = r.updates rel s env := by
  induction r generalizing k env with
  | skip => rfl
  | update f args v =>
      simp only [compile, Operational.Rule.updates, updates, Term.eval_compile rel s _ _ _ _ h]
  | parallel a b iha ihb =>
      simp only [compile, Operational.Rule.updates, updates, iha slots env values h, ihb slots env values h]
  | conditional c a b iha ihb =>
      simp only [compile, Operational.Rule.updates, updates, Term.eval_compile rel s _ _ _ _ h,
        iha slots env values h, ihb slots env values h]
  | «forall» n bound body ih =>
      simp only [compile, Operational.Rule.updates, updates, Term.eval_compile rel s _ _ _ _ h]
      congr 1
      funext x
      exact ih _ _ _ (agrees_bind h n x)
  | letValue n value body ih =>
      simp only [compile, Operational.Rule.updates, updates, Term.eval_compile rel s _ _ _ _ h]
      exact ih _ _ _ (agrees_bind h n (value.eval rel s env))

end Rule

structure Program (R : Type) where
  Functions : Type
  finiteFunctions : Fintype Functions
  arity : Functions → ℕ
  body : Rule R (Control ⊕ Functions) (Sum.elim (fun _ => 0) arity)

namespace Program

variable (P : Program R) [Fintype A]

abbrev functionArity : Control ⊕ P.Functions → ℕ := Sum.elim (fun _ => 0) P.arity

abbrev Store := State (Control ⊕ P.Functions) P.functionArity A

def flag (s : P.Store (A := A)) (c : Control) : Prop := s.value ⟨.inl c, Fin.elim0⟩ = Operational.truth

def step (rel : R → A → A → Bool) (s : P.Store (A := A)) : Option (P.Store (A := A)) :=
  if P.flag s .halt then some s else
    let u := P.body.updates rel s (fun _ => Operational.empty)
    if State.Consistent u then some (s.applyUpdates u) else none

def run (rel : R → A → A → Bool) : ℕ → Option (P.Store (A := A))
  | 0 => some State.initial
  | j+1 => (run rel j).bind (P.step rel)

def active (rel : R → A → A → Bool) (h : ℕ) : Finset (HF A) :=
  (Finset.range (h+1)).biUnion (fun j => ((P.run rel j).toFinset).biUnion State.active)

def accepts (time space : Polynomial ℕ) (rel : R → A → A → Bool) : Prop :=
  ∃ h st, h ≤ time.eval (Fintype.card A) ∧ P.run rel h = some st ∧ P.flag st .halt ∧ P.flag st .accept ∧
    (P.active rel h).card ≤ space.eval (Fintype.card A)

def compile : Operational.Machine R where
  Functions := P.Functions
  finiteFunctions := P.finiteFunctions
  arity := P.arity
  rule := P.body.compile (fun _ => none)

omit [Fintype A] in
lemma flag_compile (s : P.Store (A := A)) (c : Control) : P.compile.flag s c = P.flag s c := rfl

lemma step_compile (rel : R → A → A → Bool) (s : P.Store (A := A)) :
    P.compile.step rel s = P.step rel s := by
  change (if P.flag s .halt then some s else
    let u := (P.body.compile (fun _ => none)).updates rel s Fin.elim0
    if State.Consistent u then some (s.applyUpdates u) else none) = _
  have hu := Rule.updates_compile rel s P.body (fun _ => none)
    (fun _ => Operational.empty) Fin.elim0 (fun _ => rfl)
  dsimp only
  rw [hu]
  rfl

lemma run_compile (rel : R → A → A → Bool) (h : ℕ) :
    P.compile.run rel h = P.run rel h := by
  induction h with
  | zero => rfl
  | succ h ih =>
      simp only [Operational.Machine.run, run, ih]
      congr 1
      funext s
      exact P.step_compile rel s

lemma active_compile (rel : R → A → A → Bool) (h : ℕ) :
    P.compile.runActive rel h = P.active rel h := by
  unfold Operational.Machine.runActive active
  simp only [P.run_compile]
  congr 1
  funext j
  cases P.run rel j <;> simp ; rfl

lemma accepts_compile (time space : Polynomial ℕ) (rel : R → A → A → Bool) :
    P.compile.polynomialCumulativeAccepts time space rel ↔ P.accepts time space rel := by
  simp only [Operational.Machine.polynomialCumulativeAccepts, Operational.Machine.cumulativeAccepts,
    accepts, P.run_compile, Operational.Machine.flag, flag, P.active_compile]
  rfl

end Program

def Definable (Q : ∀ {A : Type}, [Fintype A] → Input A → Prop) : Prop :=
  ∃ P : Program Symbol, ∃ time space : Polynomial ℕ,
    ∀ (A : Type) [Fintype A] (I : Input A), P.accepts time space I.rel ↔ Q I

theorem query_not_definable : ¬ Definable (fun {_} [_] I => I.query) := by
  rintro ⟨P, time, space, h⟩
  apply query_not_polynomial_cumulative_HF
  refine ⟨P.compile, time, space, ?_⟩
  intro A inst I
  exact (P.accepts_compile time space I.rel).trans (h A I)

end

end WitnessedSeparation.FullCPT



namespace WitnessedSeparation.Operational.Machine

noncomputable section

open Classical Hereditary Counting HFCoding Finset

variable {A R : Type} [Fintype A]

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

abbrev Observer (P : Machine R) := Term R (Control ⊕ P.Functions) P.functionArity 0

abbrev instrument (P : Machine R) (O : P.Observer) : Machine R where
 Functions := P.Functions
 finiteFunctions := P.finiteFunctions
 arity := P.arity
 rule := .parallel P.rule (.letValue O .skip)

variable (P : Machine R) (O : P.Observer)

@[simp] lemma instrument_step (rel : R → A → A → Bool) (s : P.Store (A := A)) :
 (P.instrument O).step rel s = P.step rel s := by
 simp only [step,instrument,Rule.updates,union_empty]
 rfl

@[simp] lemma instrument_run (rel : R → A → A → Bool) (h : ℕ) :
 (P.instrument O).run rel h = P.run rel h := by
 induction h with
 | zero => rfl
 | succ h ih =>
   simp only [run,ih]
   congr 1
   funext s
   exact P.instrument_step O rel s

@[simp] lemma instrument_active (rel : R → A → A → Bool) (h : ℕ) :
 (P.instrument O).runActive rel h = P.runActive rel h := by
 simp only [runActive,instrument_run]
 apply biUnion_congr rfl
 intro j hj
 cases P.run rel j <;> rfl

lemma observer_trace_subset (rel : R → A → A → Bool) (s : P.Store (A := A)) :
 O.trace rel s Fin.elim0 ⊆ (P.instrument O).rule.trace rel s Fin.elim0 := by
 intro x hx
 exact mem_union_right _ (mem_union_left _ hx)

lemma original_trace_subset (rel : R → A → A → Bool) (s : P.Store (A := A)) :
 P.rule.trace rel s Fin.elim0 ⊆ (P.instrument O).rule.trace rel s Fin.elim0 := subset_union_left

def observed (rel : R → A → A → Bool) (h : ℕ) : Finset (HF A) :=
 P.runActive rel h ∪ (range h).biUnion (fun j => match P.run rel j with
  | none => ∅
  | some s => familyClosure (elements (O.eval rel s Fin.elim0)))

lemma observed_subset_trace (rel : R → A → A → Bool) (h : ℕ) :
 P.observed O rel h ⊆ (P.instrument O).runTrace rel h := by
 intro x hx
 rcases mem_union.mp hx with hx | hx
 · exact mem_union_left _ (by simpa only [instrument_active] using hx)
 · obtain ⟨j,hj,hx⟩ := mem_biUnion.mp hx
   cases hr : P.run rel j with
   | none => simp only [hr,notMem_empty] at hx
   | some s =>
     simp only [hr] at hx
     obtain ⟨y,hy,hxy⟩ := mem_familyClosure.mp hx
     have hy' := Term.closure_eval_subset_trace rel s O Fin.elim0
       (elements_subset_closure _ hy)
     have hy'' := (P.instrument O).rule_trace_subset rel (h := h) (j := j) (s := s)
       (by have := mem_range.mp hj; omega) (by simpa only [instrument_run] using hr)
       (P.observer_trace_subset O rel s hy')
     exact closure_subset_of_transitive ((P.instrument O).runTrace_closed rel h) hy'' hxy

lemma active_subset_observed (rel : R → A → A → Bool) {h j : ℕ} {s : P.Store (A := A)}
 (hj : j ≤ h) (hs : P.run rel j = some s) : s.active ⊆ P.observed O rel h :=
 (P.state_active_subset rel hj hs).trans subset_union_left

end

end WitnessedSeparation.Operational.Machine



namespace WitnessedSeparation.Operational.Term

noncomputable section

open Classical Hereditary Counting HFCoding Finset

variable {ι R F L : Type} {arity : F → ℕ} {A : ι → Type} [∀ i, Fintype (A i)]

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (rel : ∀ i, R → A i → A i → Bool) (s : ∀ i, State F arity (A i))

variable (hinput : ∀ r, UniformDefinable S m 2 (fun i v => inputRelation (rel i) r (v 0).val (v 1).val))

variable (hstate : ∀ f, UniformDefinable S m (arity f+1)
 (fun i v => (v 0).val = (s i).value ⟨f,fun j => (v j.succ).val⟩))

include hd hp ha hmem hset hinput hstate in
lemma uniform_root_members (K : ℕ) (O : Term R F arity 0) (hO : O.width ≤ m) (hm : 2 ≤ m)
 (ht : ∀ i x, x ∈ O.trace (rel i) (s i) Fin.elim0 → x ∈ d i ∧ (elements x).card ≤ K) :
 UniformDefinable S m 1 (fun i v => (v 0).val ∈ elements (O.eval (rel i) (s i) Fin.elim0)) := by
 have hg := uniform_graph d S hd hp ha hmem hset rel s hinput hstate K O hO
 have hvalue : UniformDefinable S m 1
     (fun i v => (v 0).val = O.eval (rel i) (s i) Fin.elim0) := by
   apply hg.congr
   intro i v
   have hv : (fun j : Fin 0 => (Fin.tail v j).val) = Fin.elim0 := Subsingleton.elim _ _
   constructor
   · intro h
     simpa only [hv] using graph_sound (d i) K (rel i) (s i) (hd i) O (v 0) (Fin.tail v) h
   · intro he
     obtain ⟨y,hy,hey⟩ := graph_complete (d i) K (rel i) (s i) (hd i) O (Fin.tail v)
       (by simpa only [hv] using ht i)
     rw [hv] at hey
     have hyy : y = v 0 := Subtype.ext (hey.trans he.symm)
     rwa [hyy] at hy
 have hh := ((hvalue.reindex (![0] : Fin 1 → Fin 2)).and
   (hmem.reindex (![1,0] : Fin 2 → Fin 2))).ex (by omega)
 apply hh.congr
 intro i v
 change (∃ y : Domain (d i), y.val = O.eval (rel i) (s i) Fin.elim0 ∧
   (v 0).val ∈ y.val) ↔ _
 constructor
 · rintro ⟨y,hy,hxy⟩
   change (v 0).val ∈ O.eval (rel i) (s i) Fin.elim0
   rwa [hy] at hxy
 · intro hx
   have hv : O.eval (rel i) (s i) Fin.elim0 ∈ d i :=
     (ht i _ (eval_mem_trace (rel i) (s i) O Fin.elim0)).1
   exact ⟨⟨_,hv⟩,rfl,hx⟩

end

end WitnessedSeparation.Operational.Term



namespace WitnessedSeparation.Operational.Machine

noncomputable section

open Classical Hereditary Counting HFCoding Finset

variable {R ι L : Type} {A : ι → Type} [∀ i, Fintype (A i)]

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable (P : Machine R) (O : P.Observer)

variable (d : ∀ i, Set (HF (A i))) (S : ∀ i, Counting.Structure L (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable S m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable S m 1 (fun _ v => isSet (v 0).val = true))

variable (rel : ∀ i, R → A i → A i → Bool)

variable (hinput : ∀ r, UniformDefinable S m 2 (fun i v => inputRelation (rel i) r (v 0).val (v 1).val))

include hd hp ha hmem hset hinput in
lemma uniform_observed (ss : ∀ i, ℕ → P.Store (A := A i)) (h K J : ℕ)
 (hr : ∀ i j, j ≤ h → P.run (rel i) j = some (ss i j))
 (hm : ∀ f, P.functionArity f+2+P.rule.width ≤ m) (hroom : 6 ≤ m) (hO : O.width ≤ m)
 (ht : ∀ i j, j < h → ∀ x ∈ (P.instrument O).rule.trace (rel i) (ss i j) Fin.elim0,
   x ∈ d i ∧ (elements x).card ≤ J)
 (hs : ∀ i j, j ≤ h → ∀ x ∈ (ss i j).active, x ∈ d i)
 (hK : ∀ i j, j ≤ h → (ss i j).active.card ≤ K)
 (hJ : ∀ i j, j < h → (familyClosure (elements (O.eval (rel i) (ss i j) Fin.elim0))).card ≤ J) :
 UniformDefinable S m 1 (fun i v => (v 0).val ∈ P.observed O (rel i) h) := by
 have htP : ∀ i j, j < h → ∀ x ∈ P.rule.trace (rel i) (ss i j) Fin.elim0,
     x ∈ d i ∧ (elements x).card ≤ J :=
   fun i j hj x hx => ht i j hj x (P.original_trace_subset O (rel i) (ss i j) hx)
 have hactive := P.uniform_runActive d S hd hp ha hmem hset rel hinput ss h K J hr hm hroom htP hs hK
 have hstage (j : ℕ) (hj : j ∈ range h) :
     UniformDefinable S m 1 (fun i v => (v 0).val ∈ familyClosure (elements (O.eval (rel i) (ss i j) Fin.elim0))) := by
   have hjh : j < h := mem_range.mp hj
   have hstate := P.uniform_run d S hd hp ha hmem hset rel hinput ss j J
     (fun i k hk => hr i k (by omega)) hm hroom (fun i k hk => htP i k (by omega))
   have htO : ∀ i x, x ∈ O.trace (rel i) (ss i j) Fin.elim0 → x ∈ d i ∧ (elements x).card ≤ J :=
     fun i x hx => ht i j hjh x (P.observer_trace_subset O (rel i) (ss i j) hx)
   have hroot := Term.uniform_root_members d S hd hp ha hmem hset rel (fun i => ss i j)
     hinput hstate J O hO (by omega) htO
   have hc : ∀ i x, x ∈ familyClosure (elements (O.eval (rel i) (ss i j) Fin.elim0)) → x ∈ d i := by
     intro i x hx
     obtain ⟨y,hy,hxy⟩ := mem_familyClosure.mp hx
     exact (htO i x (Term.closure_eval_subset_trace (rel i) (ss i j) O Fin.elim0
       (closure_member_subset hy hxy))).1
   have hh := State.uniform_descendants d S hmem
     (fun i => elements (O.eval (rel i) (ss i j) Fin.elim0)) hroot hc (by omega) J
   apply hh.congr
   intro i v
   rw [descendants_eq _ J (hJ i j hjh)]
 apply (hactive.or (UniformDefinable.exists_finset (range h) hstage)).congr
 intro i v
 simp only [observed,mem_union,mem_biUnion]
 apply or_congr Iff.rfl
 constructor
 · rintro ⟨j,hj,hv⟩
   exact ⟨j,hj,by simpa only [hr i j (by have := mem_range.mp hj; omega)] using hv⟩
 · rintro ⟨j,hj,hv⟩
   exact ⟨j,hj,by simpa only [hr i j (by have := mem_range.mp hj; omega)] using hv⟩

end

end WitnessedSeparation.Operational.Machine



namespace WitnessedSeparation.Grid

noncomputable section

open Classical Hereditary Counting HFCoding Operational Finset

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable {n m M N : ℕ} (P : Operational.Machine Symbol) (O : P.Observer) (vstar : Vertex n)

lemma op_observed_agrees (hn : 1 ≤ n) (h K : ℕ) (hN : 0 < N)
    (ss : ∀ i : Bool, ℕ → P.Store (A := Atom (twoCharges vstar i)))
    (hr : ∀ i j, j ≤ h → P.run (atomInput (twoCharges vstar i)).rel j = some (ss i j))
    (ha : ∀ i j, j ≤ h → (ss i j).active.card ≤ K)
    (q : ℝ) (hq : 0 ≤ q) (hb : ((h+1)*(K+(P.instrument O).rule.bound.eval K):ℝ) ≤ (N:ℝ)^q)
    (hm : ∀ f, P.functionArity f+2+(P.instrument O).rule.width ≤ m) (hroom : 6 ≤ m)
    (hs : 0 < ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊)
    (hwidth : max 4 (m+1)*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ ≤ M)
    (hhom : (7*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)+
      7*((6*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M) :
    (P.observed O (atomInput (twoCharges vstar false)).rel h).card =
      (P.observed O (atomInput (twoCharges vstar true)).rel h).card := by
  let s := ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊
  let D := programDomain (twoCharges vstar) (s := s)
  let C := programHF (twoCharges vstar) (s := s)
  have hbound (i : Bool) : ∀ j ≤ h, ∀ st, P.run (atomInput (twoCharges vstar i)).rel j = some st → st.active.card ≤ K := by
    intro j hj st hh
    have he : st = ss i j := Option.some.inj (hh.symm.trans (hr i j hj))
    exact he ▸ ha i j hj
  have hfamily (i : Bool) : ∀ x ∈ (P.instrument O).runTrace (atomInput (twoCharges vstar i)).rel h, x ∈ D i :=
    opTrace_supported (twoCharges vstar i) (P.instrument O) hn h K N hN
      (fun j hj st hh => hbound i j hj st (by simpa only [Machine.instrument_run] using hh)) q hq hb
  have ht : ∀ i j, j < h → ∀ x ∈ (P.instrument O).rule.trace (atomInput (twoCharges vstar i)).rel (ss i j) Fin.elim0,
      x ∈ D i ∧ (elements x).card ≤ (h+1)*(K+(P.instrument O).rule.bound.eval K) := by
    intro i j hj x hx
    have hx' := (P.instrument O).rule_trace_subset (h := h) (j := j) (s := ss i j) (atomInput (twoCharges vstar i)).rel (by omega) (by simpa only [Machine.instrument_run] using hr i j (by omega)) hx
    refine ⟨hfamily i x hx',?_⟩
    have he : elements x ⊆ (P.instrument O).runTrace (atomInput (twoCharges vstar i)).rel h := by
      intro y hy
      exact (P.instrument O).runTrace_closed _ h x hx' y hy
    exact (card_le_card he).trans ((P.instrument O).card_runTrace_le _ h K
      (fun j hj st hh => hbound i j hj st (by simpa only [Machine.instrument_run] using hh)))
  have hmP : ∀ f, P.functionArity f+2+P.rule.width ≤ m := by
    intro f
    have hh := hm f
    change P.functionArity f + 2 + (6 + P.rule.width + (6 + O.width + 6)) ≤ m at hh
    omega
  have hO : O.width ≤ m := by
    have hh := hm (.inl .halt)
    simp only [Machine.instrument,Rule.width] at hh
    omega
  have hJ (i : Bool) (j : ℕ) (hj : j < h) :
      (familyClosure (elements (O.eval (atomInput (twoCharges vstar i)).rel (ss i j) Fin.elim0))).card ≤
        (h+1)*(K+(P.instrument O).rule.bound.eval K) := by
    have hsub : familyClosure (elements (O.eval (atomInput (twoCharges vstar i)).rel (ss i j) Fin.elim0)) ⊆
        (P.instrument O).runTrace (atomInput (twoCharges vstar i)).rel h := by
      intro x hx
      apply P.observed_subset_trace O _ h
      exact mem_union_right _ (mem_biUnion.mpr ⟨j,mem_range.mpr hj,by simpa only [hr i j (by omega)] using hx⟩)
    exact (card_le_card hsub).trans ((P.instrument O).card_runTrace_le _ h K
      (fun j hj st hh => hbound i j hj st (by simpa only [Machine.instrument_run] using hh)))
  have hdef := P.uniform_observed O D C (program_domain_transitive (twoCharges vstar))
    (program_pure (twoCharges vstar) hn) (program_atom_mem (twoCharges vstar) hs)
    (program_mem_uniform (twoCharges vstar)) (program_set_uniform (twoCharges vstar))
    (fun i => (atomInput (twoCharges vstar i)).rel) (op_input_uniform (twoCharges vstar))
    ss h K ((h+1)*(K+(P.instrument O).rule.bound.eval K)) hr hmP hroom hO ht
    (fun i j hj x hx => hfamily i x ((P.instrument O).active_subset_trace (h := h) (j := j) (s := ss i j) _ hj
      (by simpa only [Machine.instrument_run] using hr i j hj) hx)) ha hJ
  have hc := Operational.Machine.uniform_finite_family_card D C
    (fun i => P.observed O (atomInput (twoCharges vstar i)).rel h) hdef
    (fun i x hx => hfamily i x (P.observed_subset_trace O _ h hx)) (by omega)
    (P.observed O (atomInput (twoCharges vstar false)).rel h).card
  obtain ⟨φ,hφ,hφsem⟩ := hc (Fin.elim0 : Fin 0 → Fin m)
  have hfree : φ.free = ∅ := subset_empty.mp (by simpa using hφ)
  let v : Fin m → Domain (D false) := fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn false 0⟩
  let w : Fin m → Domain (D true) := fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn true 0⟩
  let := atom_nonempty hn (0 : Vertex n → Scalar)
  let := atom_nonempty hn (Pi.single vstar 1)
  have he := (hφsem false v).symm.trans ((grid_hf_transfer hn hs (by omega) vstar
    hwidth hhom hgiant φ hfree v w).trans (hφsem true w))
  exact (he.mp rfl).symm

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Operational.Machine

noncomputable section

open Classical Hereditary Finset

variable {A R : Type} [Fintype A]

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable (P : Machine R) (O : P.Observer)

def observedAccepts (rel : R → A → A → Bool) (time space : ℕ) : Prop :=
  ∃ h st, h ≤ time ∧ P.run rel h = some st ∧ P.flag st .halt ∧ P.flag st .accept ∧
    (P.observed O rel h).card ≤ space

lemma observed_implies_bounded (rel : R → A → A → Bool) {time space : ℕ}
    (ha : P.observedAccepts O rel time space) : P.boundedAccepts rel time space := by
  obtain ⟨h,st,hht,hhr,hhf,hha,hbudget⟩ := ha
  refine ⟨h,st,hht,hhr,hhf,hha,?_⟩
  intro j hj t ht
  exact (card_le_card (P.active_subset_observed O rel hj ht)).trans hbudget

variable {B : Bool → Type} [∀ i, Fintype (B i)]

variable (rel : ∀ i, R → B i → B i → Bool)

lemma observed_accept_transfer (time space K : ℕ) (hS : space ≤ K)
    (hnext : space+P.rule.bound.eval space ≤ K)
    (hroot : ∀ i, (State.initial : P.Store (A := B i)).active.card ≤ K)
    (hobs : ∀ h, h ≤ time → P.PrefixBound rel h K → P.ObservationsAt rel h)
    (hcum : ∀ h, h ≤ time → P.PrefixBound rel h K →
      (P.observed O (rel false) h).card = (P.observed O (rel true) h).card)
    (i j : Bool) (hacc : P.observedAccepts O (rel i) time space) :
    P.observedAccepts O (rel j) time space := by
  by_cases hij : i = j
  · subst j; exact hacc
  have hcases (b : Bool) : b = i ∨ b = j := by cases i <;> cases j <;> cases b <;> simp_all
  obtain ⟨h,st,hht,hhr,hhf,hha,hbudget⟩ := hacc
  have hsource : P.observedAccepts O (rel i) h space := ⟨h,st,le_refl _,hhr,hhf,hha,hbudget⟩
  have htarget := P.bounded_accept_transfer rel h space K hS hnext hroot
    (fun k hk => hobs k (by omega)) i j (P.observed_implies_bounded O (rel i) hsource)
  have hsource' := P.bounded_active_all (rel i) (P.observed_implies_bounded O (rel i) hsource)
  have htarget' := P.bounded_active_all (rel j) htarget
  have hp : P.PrefixBound rel h K := by
    intro b k hk
    rcases hcases b with rfl | rfl
    · obtain ⟨t,ht,hb⟩ := hsource' k
      exact ⟨t,ht,hb.trans hS⟩
    · obtain ⟨t,ht,hb⟩ := htarget' k
      exact ⟨t,ht,hb.trans hS⟩
  obtain ⟨t,ht,hbt⟩ := htarget' h
  have ho := hobs h hht hp i j st t hhr ht
  have he : (P.observed O (rel i) h).card = (P.observed O (rel j) h).card := by
    have he := hcum h hht hp
    cases i <;> cases j <;> simp_all
  exact ⟨h,t,hht,ht,(ho.1 .halt).mp hhf,(ho.1 .accept).mp hha,he ▸ hbudget⟩

lemma observed_accept_iff (time space K : ℕ) (hS : space ≤ K)
    (hnext : space+P.rule.bound.eval space ≤ K)
    (hroot : ∀ i, (State.initial : P.Store (A := B i)).active.card ≤ K)
    (hobs : ∀ h, h ≤ time → P.PrefixBound rel h K → P.ObservationsAt rel h)
    (hcum : ∀ h, h ≤ time → P.PrefixBound rel h K →
      (P.observed O (rel false) h).card = (P.observed O (rel true) h).card) :
    P.observedAccepts O (rel false) time space ↔ P.observedAccepts O (rel true) time space :=
  ⟨P.observed_accept_transfer O rel time space K hS hnext hroot hobs hcum false true,
   P.observed_accept_transfer O rel time space K hS hnext hroot hobs hcum true false⟩

end





noncomputable section

def polynomialObservedAccepts {A R : Type} [Fintype A] (P : Machine R) (O : P.Observer)
 (time space : Polynomial ℕ) (rel : R → A → A → Bool) : Prop :=
 P.observedAccepts O rel (time.eval (Fintype.card A)) (space.eval (Fintype.card A))

lemma observedAccepts_fintype {A R : Type} (t u : Fintype A) (P : Machine R) (O : P.Observer)
 (rel : R → A → A → Bool) (T S : ℕ) :
 @observedAccepts A R t P O rel T S ↔ @observedAccepts A R u P O rel T S := by
 have h : t = u := Subsingleton.elim _ _
 cases h
 rfl

end

end WitnessedSeparation.Operational.Machine



namespace WitnessedSeparation.Grid

noncomputable section

open Classical Hereditary Counting HFCoding Operational Finset

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

variable {n m M N : ℕ} (P : Operational.Machine Symbol) (O : P.Observer) (vstar : Vertex n)

lemma op_prefix_observed (hn : 1 ≤ n) (h K : ℕ) (hN : 0 < N)
    (hr : P.PrefixBound (fun i => (atomInput (twoCharges vstar i)).rel) h K)
    (q : ℝ) (hq : 0 ≤ q) (hb : ((h+1)*(K+(P.instrument O).rule.bound.eval K):ℝ) ≤ (N:ℝ)^q)
    (hm : ∀ f, P.functionArity f+2+(P.instrument O).rule.width ≤ m) (hroom : 6 ≤ m)
    (hs : 0 < ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊)
    (hwidth : max 4 (m+1)*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ ≤ M)
    (hhom : (7*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)+
      7*((6*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M) :
    (P.observed O (atomInput (twoCharges vstar false)).rel h).card =
      (P.observed O (atomInput (twoCharges vstar true)).rel h).card := by
  let ss := fun i j => (P.run (atomInput (twoCharges vstar i)).rel j).getD State.initial
  have hrs : ∀ i j, j ≤ h → P.run (atomInput (twoCharges vstar i)).rel j = some (ss i j) := by
    intro i j hj
    obtain ⟨st,hst,hb⟩ := hr i j hj
    simp only [ss,hst,Option.getD_some]
  have hact : ∀ i j, j ≤ h → (ss i j).active.card ≤ K := by
    intro i j hj
    obtain ⟨st,hst,hb⟩ := hr i j hj
    simpa only [ss,hst,Option.getD_some] using hb
  exact op_observed_agrees P O vstar hn h K hN ss hrs hact q hq hb hm hroom hs hwidth hhom hgiant

end





noncomputable section

open Classical Hereditary Counting HFCoding Operational Quantitative Finset

local instance {C : Type} : DecidableEq (HF C) := Classical.decEq _

theorem polynomial_observed_agrees_on_some_box (P : Operational.Machine Symbol) (O : P.Observer) (time space : Polynomial ℕ) :
    ∃ (n : ℕ) (_hn : 1 ≤ n) (vstar : Vertex n),
      P.polynomialObservedAccepts O time space (atomInput (0 : Vertex n → Scalar)).rel ↔
        P.polynomialObservedAccepts O time space (atomInput (Pi.single vstar 1)).rel := by
  obtain ⟨ct,dt,hpt⟩ := PolynomialCost.eval_bound time
  obtain ⟨cs,ds,hps⟩ := PolynomialCost.eval_bound space
  let c := ct+cs
  let d := dt+ds
  have hmaj (N : ℕ) : time.eval N ≤ c*(N+1)^d ∧ space.eval N ≤ c*(N+1)^d := by
    constructor
    · exact (hpt N).trans (Nat.mul_le_mul (by dsimp [c]; omega)
        (Nat.pow_le_pow_right (by omega) (by dsimp [d]; omega)))
    · exact (hps N).trans (Nat.mul_le_mul (by dsimp [c]; omega)
        (Nat.pow_le_pow_right (by omega) (by dsimp [d]; omega)))
  obtain ⟨m,hroom,hm⟩ := (P.instrument O).exists_palette
  let p₀ : Polynomial ℕ := Polynomial.X+P.rule.bound
  let p : Polynomial ℕ := (Polynomial.X+1)*(p₀+(P.instrument O).rule.bound.comp p₀)
  obtain ⟨cp,dp,hp⟩ := PolynomialCost.eval_bound p
  let e := timeExponent c d+2
  let a := timeExponent cp dp
  let q := e*a
  have he : 4 ≤ e := by have := timeExponent_ge_two c d; omega
  have ha : 2 ≤ a := timeExponent_ge_two cp dp
  have hq : 0 < q := Nat.mul_pos (by omega) (by omega)
  obtain ⟨n,hn,hnum⟩ := exists_numeric_box q hq m
  let N := atomSizeConstant*(n+1)^3
  let B := N^e
  let K := B+P.rule.bound.eval B
  let vstar : Vertex n := ⟨0,0,0⟩
  let rel := fun i => (atomInput (twoCharges vstar i)).rel
  let T := time.eval (Fintype.card (Atom (0 : Vertex n → Scalar)))
  let S := space.eval (Fintype.card (Atom (0 : Vertex n → Scalar)))
  have hN : 2 ≤ N := hnum.1
  have hinput : ∀ i, Fintype.card (Atom (twoCharges vstar i)) ≤ N :=
    fun i => (atom_card_bounds hn (twoCharges vstar i)).2
  have hBB : N^timeExponent c d ≤ B := Nat.pow_le_pow_right (by omega) (by dsimp [e]; omega)
  have hB : 2 ≤ B := (polynomial_bounds c d N hN).1.trans hBB
  have hinit : N+3 ≤ B := by
    have hs : 4 ≤ N^2 := by nlinarith
    have ht := Nat.mul_le_mul_left N hs
    calc
      N+3 ≤ N^3 := by nlinarith
      _ ≤ B := Nat.pow_le_pow_right (by omega) (by omega)
  have hTB : T ≤ B := by
    exact ((PolynomialCost.eval_mono time (hinput false)).trans (hmaj N).1).trans
      ((polynomial_bounds c d N hN).2.2.1.trans hBB)
  have hSB : S ≤ B := by
    exact ((PolynomialCost.eval_mono space (hinput false)).trans (hmaj N).2).trans
      ((polynomial_bounds c d N hN).2.2.1.trans hBB)
  have hsK : S ≤ K := hSB.trans (Nat.le_add_right _ _)
  have hnext : S+P.rule.bound.eval S ≤ K :=
    add_le_add hSB (PolynomialCost.eval_mono _ hSB)
  have hroot (i : Bool) : (State.initial : P.Store (A := Atom (twoCharges vstar i))).active.card ≤ K :=
    State.initial_active_card.trans ((Nat.add_le_add_right (hinput i) 3).trans (hinit.trans (Nat.le_add_right _ _)))
  have hpoly (h : ℕ) (hh : h ≤ T) : (h+1)*(K+(P.instrument O).rule.bound.eval K) ≤ N^q := by
    calc
      (h+1)*(K+(P.instrument O).rule.bound.eval K) ≤ (B+1)*(K+(P.instrument O).rule.bound.eval K) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = p.eval B := by simp only [p,p₀,K,Polynomial.eval_mul,Polynomial.eval_add,
        Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp]
      _ ≤ cp*(B+1)^dp := hp B
      _ ≤ B^a := (polynomial_bounds cp dp B hB).2.2.1
      _ = N^q := by simp only [B,q,pow_mul]
  have hb_le (K : ℕ) : P.rule.bound.eval K ≤ (P.instrument O).rule.bound.eval K := by
    simp only [Machine.instrument,Rule.bound,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_zero]
    omega
  have hmP : ∀ f, P.functionArity f+2+P.rule.width ≤ m := by
    intro f
    have hh := hm f
    change P.functionArity f + 2 + (6 + P.rule.width + (6 + O.width + 6)) ≤ m at hh
    omega
  have hobs := fun (h : ℕ) (hht : h ≤ T) hprefix =>
    op_prefix_observations (N := N) P vstar hn h K (by omega) hprefix (q:ℝ) (by positivity)
      (by rw [Real.rpow_natCast]
          exact_mod_cast (le_trans (Nat.mul_le_mul_left (h+1) (Nat.add_le_add_left (hb_le K) K)) (hpoly h hht))) hmP hroom
      hnum.2.1 hnum.2.2.1 (by simpa only [N,Nat.cast_mul] using hnum.2.2.2.1) hnum.2.2.2.2
  have hcum := fun (h : ℕ) (hht : h ≤ T) hprefix =>
    op_prefix_observed (N := N) P O vstar hn h K (by omega) hprefix (q:ℝ) (by positivity)
      (by rw [Real.rpow_natCast]; exact_mod_cast hpoly h hht) hm hroom
      hnum.2.1 hnum.2.2.1 (by simpa only [N,Nat.cast_mul] using hnum.2.2.2.1) hnum.2.2.2.2
  have hh := P.observed_accept_iff O rel T S K hsK hnext hroot hobs hcum
  refine ⟨n,hn,vstar,?_⟩
  have hcard := atom_card_independent hn (0 : Vertex n → Scalar) (Pi.single vstar 1)
  simp only [Operational.Machine.polynomialObservedAccepts,rel,T,S,twoCharges,← hcard] at hh ⊢
  convert hh using 1 <;> apply Operational.Machine.observedAccepts_fintype

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation

theorem query_not_polynomial_observed_HF :
 ¬ ∃ (P : Operational.Machine Symbol) (O : P.Observer) (time space : Polynomial ℕ),
   ∀ (A : Type) [Fintype A] (I : Input A), P.polynomialObservedAccepts O time space I.rel ↔ I.query := by
 rintro ⟨P,O,time,space,hdecides⟩
 obtain ⟨n,hn,vstar,hagree⟩ := Grid.polynomial_observed_agrees_on_some_box P O time space
 obtain ⟨hzero,hunit⟩ := Grid.opposite_answers hn vstar
 exact hunit ((hdecides _ _).mp (hagree.mp ((hdecides _ _).mpr hzero)))

end WitnessedSeparation

end OAI
