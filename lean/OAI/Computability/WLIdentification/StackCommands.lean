import OAI.Computability.WLIdentification.TapeCompiler

namespace OAI

namespace WLIdentification

namespace StackModel

/-- Finite structured source code. Tests and registers have fixed finite range;
all unbounded data remain in the explicitly named bit stacks. -/
inductive Command (K R : Type) where
  | skip
  | push (k : K) (value : R → Bool)
  | pop (k : K) (store : R → Option Bool → R)
  | modify (store : R → R)
  | seq (first second : Command K R)
  | branch (test : R → Bool) (yes no : Command K R)
  | while (test : R → Bool) (body : Command K R)

namespace Command
variable {K R : Type}

abbrev Control : Command K R → Type
  | .skip | .push _ _ | .pop _ _ | .modify _ => Unit
  | .seq c d => Control c ⊕ Control d
  | .branch _ c d => Unit ⊕ (Control c ⊕ Control d)
  | .while _ c => Unit ⊕ Control c

noncomputable instance controlFintype (c : Command K R) : Fintype (Control c) := by
  induction c <;> simp only [Control] <;> infer_instance

def entry : (c : Command K R) → Control c
  | .skip | .push _ _ | .pop _ _ | .modify _ => ()
  | .seq c _ => .inl (entry c)
  | .branch _ _ _ | .while _ _ => .inl ()

end Command

namespace Instruction
variable {K R A B : Type}
def map (f : A → B) : Instruction K A R → Instruction K B R
  | .push k value next => .push k value (f next)
  | .pop k store next => .pop k store (f next)
  | .modify store next => .modify store (f next)
  | .branch test yes no => .branch test (f yes) (f no)
  | .halt b => .halt b

@[simp] theorem map_map {C : Type} (f : A → B) (g : B → C) (i : Instruction K A R) :
    map g (map f i) = map (g ∘ f) i := by cases i <;> rfl
@[simp] theorem map_id (i : Instruction K A R) : map id i = i := by cases i <;> rfl
end Instruction

namespace Command
variable {K R : Type}

def code : (c : Command K R) → Control c → Instruction K (Option (Control c)) R
  | .skip, _ => .modify id none
  | .push k f, _ => .push k f none
  | .pop k f, _ => .pop k f none
  | .modify f, _ => .modify f none
  | .seq c d, .inl x => (c.code x).map (fun a => a.elim (some (.inr d.entry)) (some ∘ Sum.inl))
  | .seq _ d, .inr x => (d.code x).map (Option.map Sum.inr)
  | .branch test c d, .inl _ => .branch test (some (.inr (.inl c.entry))) (some (.inr (.inr d.entry)))
  | .branch _ c _, .inr (.inl x) => (c.code x).map (Option.map (Sum.inr ∘ Sum.inl))
  | .branch _ _ d, .inr (.inr x) => (d.code x).map (Option.map (Sum.inr ∘ Sum.inr))
  | .while test c, .inl _ => .branch test (some (.inr c.entry)) none
  | .while _ c, .inr x => (c.code x).map (fun a => a.elim (some (.inl ())) (some ∘ Sum.inr))

def program (c : Command K R) (s : R) : Program K (Option (Control c)) R where
  main := some c.entry
  initialStore := s
  code
    | none => .halt true
    | some x => c.code x

/-- Execution costs count actual finite-control stack instructions. -/
inductive Exec [DecidableEq K] : Command K R → R → (K → Word) → R → (K → Word) → ℕ → Prop
  | skip (s S) : Exec .skip s S s S 1
  | push (k f s S) : Exec (.push k f) s S s (Function.update S k (S k ++ [f s])) 1
  | pop (k f s S) : Exec (.pop k f) s S (f s (S k).getLast?) (Function.update S k (S k).dropLast) 1
  | modify (f s S) : Exec (.modify f) s S (f s) S 1
  | seq {c d s S t T u U a b} : Exec c s S t T a → Exec d t T u U b →
      Exec (.seq c d) s S u U (b + a)
  | branch_true {test c d s S t T n} : test s = true → Exec c s S t T n →
      Exec (.branch test c d) s S t T (n + 1)
  | branch_false {test c d s S t T n} : test s = false → Exec d s S t T n →
      Exec (.branch test c d) s S t T (n + 1)
  | while_false (test c s S) : test s = false → Exec (.while test c) s S s S 1
  | while_true {test c s S t T u U a b} : test s = true → Exec c s S t T a →
      Exec (.while test c) t T u U b → Exec (.while test c) s S u U (b + a + 1)

variable [DecidableEq K] {Λ : Type}

/-- A compositional (not oracle) embedding of all source control locations. -/
def Embeds (P : Program K Λ R) (c : Command K R) (e : Control c → Λ) (next : Λ) : Prop :=
  ∀ x, P.code (e x) = (c.code x).map (fun a => a.elim next e)

omit [DecidableEq K] in
theorem embeds_seq_left {P : Program K Λ R} {c d : Command K R} {e : Control (.seq c d) → Λ}
    {next : Λ} (h : Embeds P (.seq c d) e next) :
    Embeds P c (e ∘ Sum.inl) (e (.inr d.entry)) := by
  intro x
  rw [Function.comp_apply, h _]
  simp only [code, Instruction.map_map]
  congr 1
  funext a
  cases a <;> rfl

omit [DecidableEq K] in
theorem embeds_seq_right {P : Program K Λ R} {c d : Command K R} {e : Control (.seq c d) → Λ}
    {next : Λ} (h : Embeds P (.seq c d) e next) :
    Embeds P d (e ∘ Sum.inr) next := by
  intro x
  rw [Function.comp_apply, h _]
  simp only [code, Instruction.map_map]
  congr 1
  funext a
  cases a <;> rfl

omit [DecidableEq K] in
theorem embeds_branch_left {P : Program K Λ R} {test : R → Bool} {c d : Command K R}
    {e : Control (.branch test c d) → Λ} {next : Λ} (h : Embeds P (.branch test c d) e next) :
    Embeds P c (e ∘ Sum.inr ∘ Sum.inl) next := by
  intro x
  rw [Function.comp_apply, Function.comp_apply, h _]
  simp only [code, Instruction.map_map]
  congr 1
  funext a
  cases a <;> rfl

omit [DecidableEq K] in
theorem embeds_branch_right {P : Program K Λ R} {test : R → Bool} {c d : Command K R}
    {e : Control (.branch test c d) → Λ} {next : Λ} (h : Embeds P (.branch test c d) e next) :
    Embeds P d (e ∘ Sum.inr ∘ Sum.inr) next := by
  intro x
  rw [Function.comp_apply, Function.comp_apply, h _]
  simp only [code, Instruction.map_map]
  congr 1
  funext a
  cases a <;> rfl

omit [DecidableEq K] in
theorem embeds_while_body {P : Program K Λ R} {test : R → Bool} {c : Command K R}
    {e : Control (.while test c) → Λ} {next : Λ} (h : Embeds P (.while test c) e next) :
    Embeds P c (e ∘ Sum.inr) (e (.inl ())) := by
  intro x
  rw [Function.comp_apply, h _]
  simp only [code, Instruction.map_map]
  congr 1
  funext a
  cases a <;> rfl

/-- This induction supplies every control-flow transition, even nested loops. -/
theorem Exec.execution {c : Command K R} {s S t T n} (h : Exec c s S t T n)
    (P : Program K Λ R) (e : Control c → Λ) (next : Λ) (he : Embeds P c e next) :
    (StackModel.step P)^[n] ⟨.inr (e c.entry), s, S⟩ = ⟨.inr next, t, T⟩ := by
  induction h generalizing next with
  | skip s S => simp only [entry, Function.iterate_one, step, he _, code, Instruction.map, Option.elim_none, id_eq]
  | push k f s S => simp only [entry, Function.iterate_one, step, he _, code, Instruction.map, Option.elim_none]
  | pop k f s S => simp only [entry, Function.iterate_one, step, he _, code, Instruction.map, Option.elim_none]
  | modify f s S => simp only [entry, Function.iterate_one, step, he _, code, Instruction.map, Option.elim_none]
  | @seq c d s S t T u U a b hc hd ihc ihd =>
    rw [Function.iterate_add_apply]
    have h1 := ihc (e ∘ Sum.inl) (e (.inr d.entry)) (embeds_seq_left he)
    have h2 := ihd (e ∘ Sum.inr) next (embeds_seq_right he)
    exact h1 ▸ h2
  | @branch_true test c d s S t T n ht hc ih =>
    rw [Function.iterate_add_apply, Function.iterate_one]
    have hs : StackModel.step P ⟨.inr (e (.inl ())), s, S⟩ =
        ⟨.inr (e (.inr (.inl c.entry))), s, S⟩ := by
      simp only [step, he _, code, Instruction.map, ht, ite_true, Option.elim_some]
    rw [show (.branch test c d : Command K R).entry = .inl () from rfl, hs]
    exact ih (e ∘ Sum.inr ∘ Sum.inl) next (embeds_branch_left he)
  | @branch_false test c d s S t T n ht hd ih =>
    rw [Function.iterate_add_apply, Function.iterate_one]
    have hs : StackModel.step P ⟨.inr (e (.inl ())), s, S⟩ =
        ⟨.inr (e (.inr (.inr d.entry))), s, S⟩ := by
      simp only [step, he _, code, Instruction.map, ht, Bool.false_eq_true, ite_false, Option.elim_some]
    rw [show (.branch test c d : Command K R).entry = .inl () from rfl, hs]
    exact ih (e ∘ Sum.inr ∘ Sum.inr) next (embeds_branch_right he)
  | while_false test c s S ht =>
    simp only [entry, Function.iterate_one, step, he _, code, Instruction.map, ht,
      Bool.false_eq_true, ite_false, Option.elim_none]
  | @while_true test c s S t T u U a b ht hc hw ihc ihw =>
    rw [Function.iterate_add_apply, Function.iterate_one]
    have hs : StackModel.step P ⟨.inr (e (.inl ())), s, S⟩ =
        ⟨.inr (e (.inr c.entry)), s, S⟩ := by
      simp only [step, he _, code, Instruction.map, ht, ite_true, Option.elim_some]
    rw [show (.while test c : Command K R).entry = .inl () from rfl, hs,
      Function.iterate_add_apply]
    have h1 := ihc (e ∘ Sum.inr) (e (.inl ())) (embeds_while_body he)
    dsimp only [Function.comp_apply] at h1
    rw [h1]
    exact ihw e next he

omit [DecidableEq K] in
theorem program_embeds (c : Command K R) (s : R) : Embeds (c.program s) c some none := by
  intro x
  simp only [program]
  have he : (fun a : Option (Control c) => a.elim none some) = id := by funext a; cases a <;> rfl
  rw [he, Instruction.map_id]

theorem Exec.run {c : Command K R} {s S t T n} (h : Exec c s S t T n) (input : K) (w : Word)
    (hS : S = Function.update (fun _ => []) input w) :
    StackModel.run (c.program s) input w (n + 1) = ⟨.inl true, t, T⟩ := by
  unfold StackModel.run
  rw [Function.iterate_succ_apply']
  have he := h.execution (c.program s) some none (program_embeds c s)
  subst S
  change StackModel.step (c.program s) ((StackModel.step (c.program s))^[n]
    ⟨.inr (some c.entry), s, Function.update (fun _ => []) input w⟩) = _
  rw [he]
  rfl

end Command
end StackModel

end WLIdentification

end OAI
