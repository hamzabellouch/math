import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientFormComparison
import OAI.Geometry.NodalSets.Spectral.SphereRayleighQuotient

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

theorem sphere_integrated_form_comparison
    (A B : IntrinsicTensor) (hA : IntrinsicTensorSmooth A) (hB : IntrinsicTensorSmooth B)
    (hAs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hBs : ∀ x alpha beta, B x alpha beta = B x beta alpha)
    (hAp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (hBp : ∀ x alpha, alpha ≠ 0 → 0 < B x alpha alpha)
    (rho sigma : Base → ℝ) (hr : Continuous rho) (hsig : Continuous sigma)
    (eps : ℝ)
    (hcomp : ∀ x : Base, (∀ alpha : SphereCotangent x,
      |B x alpha alpha-A x alpha alpha| ≤ eps*A x alpha alpha) ∧
      |sigma x-rho x| ≤ eps*rho x)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) :
    (1-eps)*sphereDirichletForm A u u ≤ sphereDirichletForm B u u ∧
    sphereDirichletForm B u u ≤ (1+eps)*sphereDirichletForm A u u ∧
    (1-eps)*sphereWeightedPairing rho u u ≤ sphereWeightedPairing sigma u u ∧
    sphereWeightedPairing sigma u u ≤ (1+eps)*sphereWeightedPairing rho u u := by
  have hIA := intrinsic_differential_pair_integrable A hA hAs hAp u u hu hu
  have hIB := intrinsic_differential_pair_integrable B hB hBs hBp u u hu hu
  have hIr := sphereWeightedPairing_integrable rho u u hr hu.continuous hu.continuous
  have hIs := sphereWeightedPairing_integrable sigma u u hsig hu.continuous hu.continuous
  have hE (x : Base) := abs_le.mp ((hcomp x).1 (sphereDifferential u x))
  have hD (x : Base) :
      (1-eps)*(rho x*u x*u x) ≤ sigma x*u x*u x ∧
      sigma x*u x*u x ≤ (1+eps)*(rho x*u x*u x) := by
    have hh := abs_le.mp (hcomp x).2
    have hlo := mul_le_mul_of_nonneg_right hh.1 (sq_nonneg (u x))
    have hhi := mul_le_mul_of_nonneg_right hh.2 (sq_nonneg (u x))
    constructor <;> nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · unfold sphereDirichletForm
    rw [← integral_const_mul]
    exact integral_mono (hIA.const_mul (1-eps)) hIB (fun x ↦ by nlinarith [hE x])
  · unfold sphereDirichletForm
    rw [← integral_const_mul]
    exact integral_mono hIB (hIA.const_mul (1+eps)) (fun x ↦ by nlinarith [hE x])
  · unfold sphereWeightedPairing
    rw [← integral_const_mul]
    exact integral_mono (hIr.const_mul (1-eps)) hIs (fun x ↦ (hD x).1)
  · unfold sphereWeightedPairing
    rw [← integral_const_mul]
    exact integral_mono hIs (hIr.const_mul (1+eps)) (fun x ↦ (hD x).2)

end
end Yau.Target

end OAI
