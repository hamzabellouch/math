import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternUniformBudget

namespace OAI

/-! # A concrete finite enumeration for every equality pattern -/

namespace Ostmann
open scoped Classical

/-- The same ambient coordinate budget covers every quotient pattern. -/
theorem movingPattern_enumeration (B : Type) [Fintype B] (b : B) (n : ℕ) :
    ∃ (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
      (_e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ B ⊕ Quotient s),
      ∀ s, N s + 1 ≤ Fintype.card B + 4 * n * 2 ^ n := by
  let N := fun s : Setoid (Bool × MovingSampleIndex n) => Fintype.card (B ⊕ Quotient s) - 1
  have hpos (s : Setoid (Bool × MovingSampleIndex n)) : 0 < Fintype.card (B ⊕ Quotient s) := by
    let : Nonempty (B ⊕ Quotient s) := ⟨Sum.inl b⟩
    exact Fintype.card_pos
  have heq (s : Setoid (Bool × MovingSampleIndex n)) :
      Fintype.card (B ⊕ Quotient s) = N s + 1 := by
    dsimp only [N]
    have hp := hpos s
    omega
  let e := fun s : Setoid (Bool × MovingSampleIndex n) => (Fintype.equivFinOfCardEq (heq s)).symm
  refine ⟨N, e, ?_⟩
  intro s
  rw [← heq s, Fintype.card_sum]
  apply Nat.add_le_add_left
  simpa only [card_movingSamplePairIndex] using Fintype.card_quotient_le s

end Ostmann

end OAI
