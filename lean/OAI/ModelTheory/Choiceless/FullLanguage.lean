import OAI.ModelTheory.Choiceless.LowerBound

namespace OAI

namespace CPTSeparation.FullCPT

noncomputable section

open Classical Hereditary Finset

open Operational (State Control Location Update)

attribute [local instance] CPTSeparation.FullCPT.instDecidableEqHF

variable {A R F : Type} {arity : F → ℕ}

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

namespace Rule

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

namespace Program

variable (P : Program R) [finiteA : Fintype A]

def accepts (time space : Polynomial ℕ) (rel : R → A → A → Bool) : Prop :=
  ∃ h st, h ≤ time.eval (Fintype.card A) ∧ P.run rel h = some st ∧ P.flag st .halt ∧ P.flag st .accept ∧
    (P.active rel h).card ≤ space.eval (Fintype.card A)

def compile : Operational.Machine R where
  Functions := P.Functions
  finiteFunctions := P.finiteFunctions
  arity := P.arity
  rule := P.body.compile (fun _ => none)

omit A R P in
lemma flag_compile
    {A : Type}
    {R : Type}
    (P : FullCPT.Program R)
    [Fintype A] (s : P.Store (A := A)) (c : Control) : P.compile.flag s c = P.flag s c := rfl

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

end CPTSeparation.FullCPT

end OAI
