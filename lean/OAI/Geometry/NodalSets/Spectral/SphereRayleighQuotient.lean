import OAI.Geometry.NodalSets.Elliptic.IntrinsicGreenTesting

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

def sphereDirichletForm (A : IntrinsicTensor) (u v : Base → ℝ) : ℝ :=
  ∫ x, A x (sphereDifferential u x) (sphereDifferential v x) ∂sphereReferenceMeasure

def sphereRayleighQuotient (A : IntrinsicTensor) (rho u : Base → ℝ) : ℝ :=
  sphereDirichletForm A u u / sphereWeightedPairing rho u u

lemma sphereDirichletForm_symm (A : IntrinsicTensor)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha) (u v : Base → ℝ) :
    sphereDirichletForm A u v = sphereDirichletForm A v u :=
  integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ hs x _ _))

lemma intrinsic_quadratic_nonneg (A : IntrinsicTensor)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha) (x : Base) (alpha : SphereCotangent x) :
    0 ≤ A x alpha alpha := by
  by_cases hz : alpha = 0
  · simp [hz]
  · exact (hp x alpha hz).le

lemma sphereDirichletForm_nonneg (A : IntrinsicTensor)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha) (u : Base → ℝ) :
    0 ≤ sphereDirichletForm A u u :=
  integral_nonneg (fun x ↦ intrinsic_quadratic_nonneg A hp x _)

theorem sphereRayleighQuotient_eigenfunction (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hne : u ≠ 0) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho u p z =
      lam*u ((extChartAt (𝓡 4) p).symm z)) :
    sphereRayleighQuotient A rho u = lam := by
  have h := (intrinsic_green_eigenfunction_test A hA hs hp rho hr hrp u u hu hu lam he).2.2
  unfold sphereRayleighQuotient sphereDirichletForm
  rw [h]
  exact mul_div_cancel_right₀ lam (sphereWeightedPairing_self_pos rho u hr.continuous hrp hu.continuous hne).ne'

theorem intrinsic_eigenfunctions_orthogonal (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (lam mu : ℝ) (hne : lam ≠ mu)
    (heu : ∀ p z, -intrinsicWeightedChartOperator A rho u p z =
      lam*u ((extChartAt (𝓡 4) p).symm z))
    (hev : ∀ p z, -intrinsicWeightedChartOperator A rho v p z =
      mu*v ((extChartAt (𝓡 4) p).symm z)) : sphereWeightedPairing rho u v = 0 := by
  have h1 := (intrinsic_green_eigenfunction_test A hA hs hp rho hr hrp v u hv hu lam heu).2.2
  have h2 := (intrinsic_green_eigenfunction_test A hA hs hp rho hr hrp u v hu hv mu hev).2.2
  change sphereDirichletForm A v u = _ at h1
  change sphereDirichletForm A u v = _ at h2
  rw [sphereDirichletForm_symm A hs v u,sphereWeightedPairing_symm rho v u,h2] at h1
  exact (mul_eq_zero.mp (show (lam-mu)*sphereWeightedPairing rho u v=0 by nlinarith [h1])).resolve_left
    (sub_ne_zero.mpr hne)

end
end Yau.Target

end OAI
