import OAI.NumberTheory.Ostmann.Construction.GroupedPivotPhase

namespace OAI

/-! # The retained grouped phase is the phase in the exact copy identity -/

namespace Ostmann

open scoped BigOperators Classical

theorem retainedGroupedPhase_split {H Y : Type*} [Fintype H] [Fintype Y]
    (q : H ⊕ Y → ℕ) [∀ i, Fact (q i).Prime]
    (χ : (H ⊕ Y) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (t : ∀ p : ℕ, ZMod p) (ν : H ⊕ Y → ℂ)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (M : ℕ) (v : ℤ) :
    retainedGroupedPhase q (fun i => χ i (q i)) (fun i => t (q i)) ν b M v =
      retainedPrimePhase (fun h => q (.inl h)) (fun y => q (.inr y)) t
        (fun h => χ (.inl h)) (fun y => χ (.inr y)) b
        (fun h => ν (.inl h)) (fun y => ν (.inr y)) M v := by
  have hq : q = Sum.elim (fun h => q (.inl h)) (fun y => q (.inr y)) := by
    funext i
    cases i <;> rfl
  have hcoH (h : H) : tupleCofactor q (.inl h) =
      tupleCofactor (fun h => q (.inl h)) h * ∏ y, q (.inr y) := by
    conv_lhs => rw [hq]
    exact tupleCofactor_sum_left _ _ h (NeZero.ne _)
  have hcoY (y : Y) : tupleCofactor q (.inr y) =
      (∏ h, q (.inl h)) * tupleCofactor (fun y => q (.inr y)) y := by
    conv_lhs => rw [hq]
    exact tupleCofactor_sum_right _ _ y (NeZero.ne _)
  have henv {p : ℕ} : (fun j => (q j : ZMod p)) =
      Sum.elim (fun h => (q (.inl h) : ZMod p)) (fun y => (q (.inr y) : ZMod p)) := by
    funext j
    cases j <;> rfl
  have hvD {p : ℕ} (D : ZMod p) : D⁻¹ * (v : ZMod p) = (v : ZMod p) * D⁻¹ := mul_comm _ _
  simp only [retainedGroupedPhase, Fintype.prod_sum_type, hcoH, hcoY,
    retainedPrimePhase, retainedAdditiveBranch, retainedCharacterBranch,
    henv, div_eq_mul_inv, hvD, mul_assoc, Finset.prod_mul_distrib]
  ring

end Ostmann

end OAI
