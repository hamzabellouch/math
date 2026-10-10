import OAI.NumberTheory.Ostmann.Characters.SparseTruncatedOperator

namespace OAI

/-! # Pairing the truncated kernel against only its active centered modes -/

namespace Ostmann
open WithLp
open scoped Classical BigOperators ComplexConjugate

noncomputable def countingVectorNorm {α : Type*} [Fintype α] (f : α → ℂ) : ℝ :=
  ‖(toLp 2 f : EuclideanSpace ℂ α)‖

theorem countingVectorNorm_sq {α : Type*} [Fintype α] (f : α → ℂ) :
    countingVectorNorm f ^ 2 = ∑ x, ‖f x‖ ^ 2 := EuclideanSpace.norm_sq_eq _

theorem finiteKernelOperator_pairing_le {α β : Type*} [Fintype α] [Fintype β]
    (M : α → β → ℂ) (f : α → ℂ) (g : β → ℂ) :
    ‖∑ x, conj (f x) * ∑ y, M x y * g y‖ ≤
      ‖finiteKernelOperator M‖ * countingVectorNorm f * countingVectorNorm g := by
  have he : (∑ x, conj (f x) * ∑ y, M x y * g y) =
      inner ℂ (toLp 2 f : EuclideanSpace ℂ α)
        (finiteKernelOperator M (toLp 2 g)) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply', finiteKernelOperator_apply]
  rw [he]
  calc
    _ ≤ countingVectorNorm f * ‖finiteKernelOperator M (toLp 2 g)‖ := norm_inner_le_norm _ _
    _ ≤ countingVectorNorm f * (‖finiteKernelOperator M‖ * countingVectorNorm g) :=
      mul_le_mul_of_nonneg_left ((finiteKernelOperator M).le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

noncomputable def lowModeVector {n : ℕ} {p : Fin n → ℕ}
    (K : ℕ) (f : (∀ i, Option (ZMod (p i))) → ℂ) (x : ∀ i, Option (ZMod (p i))) : ℂ :=
  if (centeredCoordinateSupport x).card ≤ K then f x else 0

theorem truncatedSparseTensorKernel_pairing {n : ℕ}
    (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ)
    (f g : (∀ i, Option (ZMod (p i))) → ℂ) :
    (∑ x, conj (f x) * ∑ y, truncatedSparseTensorKernel p S K x y * g y) =
      ∑ x, conj (lowModeVector (2 * K) f x) *
        ∑ y, truncatedSparseTensorKernel p S K x y * lowModeVector (2 * K) g y := by
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : (centeredCoordinateSupport x).card ≤ 2 * K
  · by_cases hy : (centeredCoordinateSupport y).card ≤ 2 * K
    · simp only [lowModeVector, hx, hy, ite_true]
    · have hz := truncatedSparseTensorKernel_mode_support p S K x y (Or.inr (by omega))
      simp only [hz, mul_zero, zero_mul]
  · have hz := truncatedSparseTensorKernel_mode_support p S K x y (Or.inl (by omega))
    simp only [hz, mul_zero, zero_mul]

theorem truncatedSparseTensorKernel_pairing_le {n : ℕ}
    (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ)
    (f g : (∀ i, Option (ZMod (p i))) → ℂ) :
    ‖∑ x, conj (f x) * ∑ y, truncatedSparseTensorKernel p S K x y * g y‖ ≤
      ‖finiteKernelOperator (truncatedSparseTensorKernel p S K)‖ *
        countingVectorNorm (lowModeVector (2 * K) f) *
        countingVectorNorm (lowModeVector (2 * K) g) := by
  rw [truncatedSparseTensorKernel_pairing]
  exact finiteKernelOperator_pairing_le _ _ _

end Ostmann

end OAI
