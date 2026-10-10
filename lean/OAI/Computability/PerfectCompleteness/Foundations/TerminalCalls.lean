import Mathlib.Algebra.BigOperators.Intervals
import OAI.Computability.PerfectCompleteness.Sampling.RecordSeedSamplingLemmas

namespace OAI

section

namespace PerfectCompleteness.TerminalCalls

open RecursiveSpaces DescendantSpaces RecursiveSampler
open scoped BigOperators

universe u w

variable {branch : Nat → Nat} {n m : Nat}

def TerminalIndex (repeats : Nat → Nat) : {n m : Nat} → Path branch n m → Type
  | _, _, .refl _ => Unit
  | n + 1, _, .step _ p =>
      (Fin (repeats (n + 1)) × Bool) × TerminalIndex repeats p

noncomputable instance terminalIndexFintype (repeats : Nat → Nat) (p : Path branch n m) :
    Fintype (TerminalIndex repeats p) := by
  induction p with
  | refl n => exact inferInstanceAs (Fintype Unit)
  | @step n m i p ih =>
      letI : Fintype (TerminalIndex repeats p) := ih
      exact inferInstanceAs (Fintype
        ((Fin (repeats (n + 1)) × Bool) × TerminalIndex repeats p))

noncomputable instance terminalIndexDecidableEq (repeats : Nat → Nat)
    (p : Path branch n m) : DecidableEq (TerminalIndex repeats p) := by
  induction p with
  | refl n => exact inferInstanceAs (DecidableEq Unit)
  | @step n m i p ih =>
      letI : DecidableEq (TerminalIndex repeats p) := ih
      exact inferInstanceAs (DecidableEq
        ((Fin (repeats (n + 1)) × Bool) × TerminalIndex repeats p))

def drawIndex (repeats : Nat → Nat) : {n m : Nat} → (p : Path branch n m) →
    TerminalIndex repeats p → DrawIndex repeats p
  | _, _, .refl _, terminal => terminal
  | _, _, .step _ p, terminal => .inr (terminal.1, drawIndex repeats p terminal.2)

@[simp] theorem drawIndex_refl (repeats : Nat → Nat)
    (terminal : TerminalIndex (branch := branch) repeats (.refl n)) :
    drawIndex (branch := branch) repeats (.refl n) terminal = terminal := rfl

@[simp] theorem drawIndex_step (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (terminal : TerminalIndex repeats (.step i p)) :
    drawIndex repeats (.step i p) terminal =
      .inr (terminal.1, drawIndex repeats p terminal.2) := rfl

theorem drawIndex_injective (repeats : Nat → Nat) (p : Path branch n m) :
    Function.Injective (drawIndex repeats p) := by
  induction p with
  | refl n => exact fun _ _ h => h
  | @step n m i p ih =>
      intro a b h
      have heq := Sum.inr.inj h
      apply Prod.ext
      · exact congrArg
          (fun z : (Fin (repeats (n + 1)) × Bool) × DrawIndex repeats p => z.1) heq
      · exact ih (congrArg
          (fun z : (Fin (repeats (n + 1)) × Bool) × DrawIndex repeats p => z.2) heq)

def terminalEmbedding (repeats : Nat → Nat) (p : Path branch n m) :
    TerminalIndex repeats p ↪ DrawIndex repeats p :=
  ⟨drawIndex repeats p, drawIndex_injective repeats p⟩

def IsTerminal (repeats : Nat → Nat) : {n m : Nat} → (p : Path branch n m) →
    DrawIndex repeats p → Prop
  | _, _, .refl _, _ => True
  | _, _, .step _ p, j =>
      match j with
      | .inl _ => False
      | .inr j => IsTerminal repeats p j.2

@[simp] theorem isTerminal_refl (repeats : Nat → Nat)
    (j : DrawIndex (branch := branch) repeats (.refl n)) :
    IsTerminal (branch := branch) repeats (.refl n) j := True.intro

@[simp] theorem not_isTerminal_ordinary (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (j : OffPath i) :
    ¬ IsTerminal repeats (.step i p) (.inl j) := id

@[simp] theorem isTerminal_recursive (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (call : Fin (repeats (n + 1)) × Bool)
    (j : DrawIndex repeats p) :
    IsTerminal repeats (.step i p) (.inr (call, j)) ↔ IsTerminal repeats p j := Iff.rfl

theorem isTerminal_iff_exists (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ j : DrawIndex repeats p,
      IsTerminal repeats p j ↔ ∃ terminal, drawIndex repeats p terminal = j := by
  induction p with
  | refl n =>
      intro j
      constructor
      · intro _
        exact ⟨j, rfl⟩
      · intro _
        exact True.intro
  | step i p ih =>
      intro j
      cases j with
      | inl j =>
          constructor
          · intro h
            exact False.elim h
          · rintro ⟨terminal, h⟩
            change (Sum.inr (terminal.1, drawIndex repeats p terminal.2) :
              DrawIndex repeats (.step i p)) = Sum.inl j at h
            exact Sum.inr_ne_inl h
      | inr j =>
          constructor
          · intro h
            obtain ⟨terminal, heq⟩ := (ih j.2).mp h
            refine ⟨(j.1, terminal), ?_⟩
            exact congrArg Sum.inr (Prod.ext rfl heq)
          · rintro ⟨terminal, h⟩
            exact (ih j.2).mpr
              ⟨terminal.2, congrArg Prod.snd (Sum.inr.inj h)⟩

theorem isTerminal_drawIndex (repeats : Nat → Nat) (p : Path branch n m)
    (terminal : TerminalIndex repeats p) :
    IsTerminal repeats p (drawIndex repeats p terminal) :=
  (isTerminal_iff_exists repeats p _).mpr ⟨terminal, rfl⟩

noncomputable def terminalSubtypeEquiv (repeats : Nat → Nat) (p : Path branch n m) :
    TerminalIndex repeats p ≃ {j : DrawIndex repeats p // IsTerminal repeats p j} :=
  Equiv.ofBijective
    (fun terminal => ⟨drawIndex repeats p terminal, isTerminal_drawIndex repeats p terminal⟩)
    ⟨fun _ _ h => drawIndex_injective repeats p (congrArg Subtype.val h), by
      rintro ⟨j, hj⟩
      obtain ⟨terminal, heq⟩ := (isTerminal_iff_exists repeats p j).mp hj
      exact ⟨terminal, Subtype.ext heq⟩⟩

@[simp] theorem terminalSubtypeEquiv_apply (repeats : Nat → Nat) (p : Path branch n m)
    (terminal : TerminalIndex repeats p) :
    (terminalSubtypeEquiv repeats p terminal).val = drawIndex repeats p terminal := rfl

@[simp] theorem card_refl (repeats : Nat → Nat) :
    Fintype.card (TerminalIndex (branch := branch) repeats (.refl n)) = 1 := by
  change Fintype.card Unit = 1
  exact Fintype.card_unit

theorem card_step (repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m) :
    Fintype.card (TerminalIndex repeats (.step i p)) =
      (2 * repeats (n + 1)) * Fintype.card (TerminalIndex repeats p) := by
  change Fintype.card ((Fin (repeats (n + 1)) × Bool) × TerminalIndex repeats p) = _
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  exact congrArg (fun a => a * Fintype.card (TerminalIndex repeats p)) (Nat.mul_comm _ _)

theorem card_eq_prod (repeats : Nat → Nat) (p : Path branch n m) :
    Fintype.card (TerminalIndex repeats p) = ∏ h ∈ Finset.Ioc m n, 2 * repeats h := by
  induction p with
  | refl n => simp only [card_refl, Finset.Ioc_self, Finset.prod_empty]
  | step i p ih =>
      rw [card_step, ih, Finset.prod_Ioc_succ_top p.height_le]
      exact Nat.mul_comm _ _

theorem drawSpace_eq_terminal (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u) (terminal : TerminalIndex repeats p),
      DrawSpace 𝕜 repeats p A (drawIndex repeats p terminal) =
        space 𝕜 branch m (p.family A) := by
  induction p with
  | refl n => intro A terminal; rfl
  | step i p ih =>
      intro A terminal
      exact ih (childFamily A i) terminal.2

noncomputable def terminalSpaceEquiv (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) (terminal : TerminalIndex repeats p) :
    DrawSpace 𝕜 repeats p A (drawIndex repeats p terminal) ≃
      space 𝕜 branch m (p.family A) :=
  Equiv.cast (drawSpace_eq_terminal 𝕜 repeats p A terminal)

end PerfectCompleteness.TerminalCalls

end

end OAI
