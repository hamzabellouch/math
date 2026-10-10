import OAI.Geometry.EinsteinFour.HighestMinus

namespace OAI

/-! The original derivative-slot curvature form on the highest tensors. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- Twice the diagonal curvature-block contribution on the derivative slots. -/
def derivativeSlotForm (s : Fin 3) (X : Hessian) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    quaternionMatrix s i k * quaternionMatrix s j l * matrixPairing (X k l) (X i j)

/-- The coefficient of the diagonal matrix-slot curvature form. -/
def matrixSlotForm (s : Fin 3) (X : Hessian) : ℝ :=
  ∑ i, ∑ j, ∑ b, X i j s b ^ 2

private theorem curvature_identity_zero (c : Fin 21 → ℝ) :
    10 * derivativeSlotForm 0 (highest c) + 40 * matrixSlotForm 0 (highest c) +
      hessianNormSq (totalPlus 0 (highest c)) = 26 * hessianNormSq (highest c) := by
  rw [totalPlus_highest]
  simp [derivativeSlotForm, matrixSlotForm, hessianNormSq_derivative_order,
    quaternionMatrix, Fin.sum_univ_succ]
  simp only [matrixPairing_coordinates, matrixNormSq_coordinates]
  simp [ofCoordinates]
  ring

private theorem curvature_identity_one (c : Fin 21 → ℝ) :
    10 * derivativeSlotForm 1 (highest c) + 40 * matrixSlotForm 1 (highest c) +
      hessianNormSq (totalPlus 1 (highest c)) = 26 * hessianNormSq (highest c) := by
  rw [totalPlus_highest]
  simp [derivativeSlotForm, matrixSlotForm, hessianNormSq_derivative_order,
    quaternionMatrix, Fin.sum_univ_succ]
  simp only [matrixPairing_coordinates, matrixNormSq_coordinates]
  simp [ofCoordinates]
  ring

private theorem curvature_identity_two (c : Fin 21 → ℝ) :
    10 * derivativeSlotForm 2 (highest c) + 40 * matrixSlotForm 2 (highest c) +
      hessianNormSq (totalPlus 2 (highest c)) = 26 * hessianNormSq (highest c) := by
  rw [totalPlus_highest]
  simp [derivativeSlotForm, matrixSlotForm, hessianNormSq_derivative_order,
    quaternionMatrix, Fin.sum_univ_succ]
  simp only [matrixPairing_coordinates, matrixNormSq_coordinates]
  simp [ofCoordinates]
  ring

/-- Exact curvature compression, derived from the constrained coordinates. -/
theorem curvature_form_identity (c : Fin 21 → ℝ) (t : Fin 3 → ℝ)
    (ht : ∑ s, t s = 0) :
    (1 / 2 : ℝ) * ∑ s, t s * derivativeSlotForm s (highest c) +
      2 * ∑ s, t s * matrixSlotForm s (highest c) =
        -(∑ s, t s * hessianNormSq (totalPlus s (highest c))) / 20 := by
  have h0 := congrArg (fun z : ℝ => t 0 * z) (curvature_identity_zero c)
  have h1 := congrArg (fun z : ℝ => t 1 * z) (curvature_identity_one c)
  have h2 := congrArg (fun z : ℝ => t 2 * z) (curvature_identity_two c)
  have htrace := congrArg (fun z : ℝ => 26 * hessianNormSq (highest c) * z) ht
  simp only [Fin.sum_univ_three] at ht htrace ⊢
  nlinarith

/-- The original plus part `4 − (5/6)T_D − (5/3)B_F(T)`. -/
def originalPlusCurvatureForm (t : Fin 3 → ℝ) (X : Hessian) : ℝ :=
  4 * hessianNormSq X - (5 / 12) * (∑ s, t s * derivativeSlotForm s X) -
    (5 / 3) * (∑ s, t s * matrixSlotForm s X)

/-- Exact identification of the original plus curvature form with its total
rotation expression; no representation-theoretic premise is used. -/
theorem originalPlusCurvatureForm_eq (c : Fin 21 → ℝ) (t : Fin 3 → ℝ)
    (ht : ∑ s, t s = 0) :
    originalPlusCurvatureForm t (highest c) = 4 * hessianNormSq (highest c) +
      (∑ s, t s * hessianNormSq (totalPlus s (highest c))) / 24 := by
  have h := curvature_form_identity c t ht
  unfold originalPlusCurvatureForm
  linarith

/-- The quadratic form after the two exact Casimir normalizations. -/
def casimirCurvatureForm (t u : Fin 3 → ℝ) (X : Hessian) : ℝ :=
  4 * hessianNormSq X +
    (∑ s, t s * hessianNormSq (totalPlus s X)) / 24 +
    (∑ s, u s * hessianNormSq (totalMinus s X)) / 4

/-- Sectional spectral bounds give the sharp coercive constant. -/
theorem casimirCurvatureForm_lower (c : Fin 21 → ℝ) (t u : Fin 3 → ℝ)
    (x y : ℝ) (ht : ∀ s, -x ≤ t s) (hu : ∀ s, -y ≤ u s) :
    (4 - 2 * x - 2 * y) * hessianNormSq (highest c) ≤
      casimirCurvatureForm t u (highest c) := by
  have hp := plus_energy_bound c t x ht
  have hm := minus_energy_bound c u y hu
  simp [casimirCurvatureForm, Fin.sum_univ_succ]
  nlinarith

/-- Positivity on the whole closed sectional domain, including its boundary. -/
theorem casimirCurvatureForm_nonneg (c : Fin 21 → ℝ) (t u : Fin 3 → ℝ)
    (x y : ℝ) (ht : ∀ s, -x ≤ t s) (hu : ∀ s, -y ≤ u s)
    (hxy : x + y ≤ 2) : 0 ≤ casimirCurvatureForm t u (highest c) := by
  have h := casimirCurvatureForm_lower c t u x y ht hu
  have hn : 0 ≤ hessianNormSq (highest c) := by
    unfold hessianNormSq
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc : 0 ≤ 4 - 2 * x - 2 * y := by linarith
  exact (mul_nonneg hc hn).trans h

/-- The original-form identity for any tensor satisfying the actual local
symmetry, trace and Bianchi constraints. -/
theorem originalPlusCurvatureForm_eq_of_condition (X : Hessian) (hX : condition X)
    (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0) :
    originalPlusCurvatureForm t X = 4 * hessianNormSq X +
      (∑ s, t s * hessianNormSq (totalPlus s X)) / 24 := by
  obtain ⟨c, rfl⟩ := exists_highest X hX
  exact originalPlusCurvatureForm_eq c t ht

theorem casimirCurvatureForm_nonneg_of_condition (X : Hessian) (hX : condition X)
    (t u : Fin 3 → ℝ) (x y : ℝ)
    (ht : ∀ s, -x ≤ t s) (hu : ∀ s, -y ≤ u s) (hxy : x + y ≤ 2) :
    0 ≤ casimirCurvatureForm t u X := by
  obtain ⟨c, rfl⟩ := exists_highest X hX
  exact casimirCurvatureForm_nonneg c t u x y ht hu hxy

end
end PositiveEinsteinFour.HighestHessian

end OAI
