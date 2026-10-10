import OAI.Geometry.EinsteinFour.HighestCurvature

namespace OAI

/-! Identification of the actual anti-self-dual derivative curvature term. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- The uncontracted right-quaternion curvature on the two derivative slots. -/
def rightDerivativeSlotForm (s : Fin 3) (X : Hessian) : ℝ :=
  ∑ a, ∑ b, ∑ i, ∑ j, ∑ k, ∑ l,
    rightQuaternion s i k * rightQuaternion s j l * X k l a b * X i j a b

private theorem totalMinus_slice_square (s : Fin 3) (X : Hessian) (a b : Fin 3) :
    (∑ i, ∑ j, totalMinus s X i j a b ^ 2) =
      2 * (∑ i, ∑ j, X i j a b ^ 2) -
        2 * (∑ i, ∑ j, ∑ k, ∑ l,
          rightQuaternion s i k * rightQuaternion s j l * X k l a b * X i j a b) := by
  fin_cases s <;> simp [totalMinus, rightQuaternion, Fin.sum_univ_succ] <;> ring

/-- A single generator square is the actual derivative curvature contraction.
This identity holds on the full tensor space, before imposing Bianchi. -/
theorem totalMinus_square (s : Fin 3) (X : Hessian) :
    hessianNormSq (totalMinus s X) =
      2 * hessianNormSq X - 2 * rightDerivativeSlotForm s X := by
  unfold hessianNormSq rightDerivativeSlotForm
  simp_rw [totalMinus_slice_square]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The anti-self-dual curvature term, with the normalization of equation (11). -/
def minusDerivativeCurvatureForm (u : Fin 3 → ℝ) (X : Hessian) : ℝ :=
  (1 / 2) * ∑ s, u s * rightDerivativeSlotForm s X

theorem minusDerivativeCurvatureForm_eq (u : Fin 3 → ℝ) (hu : ∑ s, u s = 0)
    (X : Hessian) :
    minusDerivativeCurvatureForm u X =
      -(∑ s, u s * hessianNormSq (totalMinus s X)) / 4 := by
  simp only [totalMinus_square]
  have htrace := congrArg (fun r : ℝ => r * hessianNormSq X) hu
  simp only [minusDerivativeCurvatureForm, Fin.sum_univ_three] at htrace ⊢
  nlinarith

/-- The complete original curvature form on an actual four-slot tensor. -/
def originalCurvatureForm (t u : Fin 3 → ℝ) (X : Hessian) : ℝ :=
  originalPlusCurvatureForm t X - minusDerivativeCurvatureForm u X

/-- Both curvature contractions agree exactly with the computed total actions. -/
theorem originalCurvatureForm_eq (X : Hessian) (hX : condition X)
    (t u : Fin 3 → ℝ) (ht : ∑ s, t s = 0) (hu : ∑ s, u s = 0) :
    originalCurvatureForm t u X = casimirCurvatureForm t u X := by
  rw [originalCurvatureForm, originalPlusCurvatureForm_eq_of_condition X hX t ht,
    minusDerivativeCurvatureForm_eq u hu X]
  unfold casimirCurvatureForm
  ring

/-- Positivity of the tensor curvature form. -/
theorem originalCurvatureForm_nonneg (X : Hessian) (hX : condition X)
    (t u : Fin 3 → ℝ) (ht : ∑ s, t s = 0) (hu : ∑ s, u s = 0)
    (x y : ℝ) (htx : ∀ s, -x ≤ t s) (huy : ∀ s, -y ≤ u s)
    (hxy : x + y ≤ 2) : 0 ≤ originalCurvatureForm t u X := by
  rw [originalCurvatureForm_eq X hX t u ht hu]
  exact casimirCurvatureForm_nonneg_of_condition X hX t u x y htx huy hxy

/-- The precise coercive constant is retained, for use before integration. -/
theorem originalCurvatureForm_lower (X : Hessian) (hX : condition X)
    (t u : Fin 3 → ℝ) (ht : ∑ s, t s = 0) (hu : ∑ s, u s = 0)
    (x y : ℝ) (htx : ∀ s, -x ≤ t s) (huy : ∀ s, -y ≤ u s) :
    (4 - 2 * x - 2 * y) * hessianNormSq X ≤ originalCurvatureForm t u X := by
  rw [originalCurvatureForm_eq X hX t u ht hu]
  obtain ⟨c, rfl⟩ := exists_highest X hX
  exact casimirCurvatureForm_lower c t u x y htx huy

end
end PositiveEinsteinFour.HighestHessian

end OAI
