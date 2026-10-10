import OAI.NumberTheory.Ostmann.Construction.RegularInitialAmplitude
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalSampleExpansion

namespace OAI

/-! # The outside spectator factors in the initial Poisson coefficient -/

namespace Ostmann
open scoped Classical BigOperators

/-- The outside cofactor units are exactly the ones used by the initial
full-tuple Fourier transform. -/
theorem initial_outside_transform {I : Type*} [Fintype I]
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ)
    (hDq : ∀ i, (Dq i : ZMod (q i)) = (tupleCofactor q i : ℕ))
    (R : ℕ) (s : ℤ) :
    (∏ i, g i ((s : ZMod (q i)) / ((Dq i : ZMod (q i)) * (R : ZMod (q i))))) =
      movingRegularTransform q g R s := by
  unfold movingRegularTransform
  apply Finset.prod_congr rfl
  intro i _
  rw [hDq i]
  simp only [div_eq_mul_inv, Nat.cast_mul, mul_comm]

/-- Rescaling the parameter by the outside product preserves precisely the
`dR/X` argument and hence the square-root normalization in (7.9). -/
theorem normalizedFourierProfile_outside_scale (ψ : ℝ → ℂ) (s X d R : ℝ) :
    normalizedFourierProfile ψ s (R / (X / d)) =
      normalizedFourierProfile ψ s (d * R / X) := by
  congr 1
  rw [div_div_eq_mul_div]
  ring

theorem movingFourierLeaf_outside_scale {σ : Type*} (value : σ → ℕ)
    (ψ : ℝ → ℂ) (X d : ℝ) (x : MovingSlotState σ) (s : ℤ) :
    movingFourierLeaf value ψ (X / d) x s =
      normalizedFourierProfile ψ s (d * (movingSlotModulus value x : ℝ) / X) :=
  normalizedFourierProfile_outside_scale ψ s X d (movingSlotModulus value x)

end Ostmann

end OAI
