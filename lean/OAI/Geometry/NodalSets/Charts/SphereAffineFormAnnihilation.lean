import OAI.Geometry.NodalSets.Charts.SphereEnergyForm
import OAI.Geometry.NodalSets.Elliptic.IntrinsicGreenTesting

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem sphere_affine_form_annihilates (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (a b : Base → ℝ) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (lam t : ℝ) (ht : t ≠ 0)
    (hAt : IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x))
    (hst : ∀ x alpha beta, (A x+roundTensorPerturbation (fun y ↦ t*a y) x) alpha beta =
      (A x+roundTensorPerturbation (fun y ↦ t*a y) x) beta alpha)
    (hpt : ∀ x alpha, alpha ≠ 0 → 0 < (A x+roundTensorPerturbation (fun y ↦ t*a y) x) alpha alpha)
    (hrpt : ∀ x, 0 < rho x+t*b x)
    (w f : Base → ℝ) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f)
    (hew : ∀ p z, -intrinsicWeightedChartOperator
      (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x)
      (fun x ↦ rho x+t*b x) w p z = lam*w ((extChartAt (𝓡 4) p).symm z))
    (hef : ∀ p z, -intrinsicWeightedChartOperator A rho f p z =
      lam*f ((extChartAt (𝓡 4) p).symm z)) :
    sphereEnergyForm a b lam w f = 0 := by
  let At : IntrinsicTensor := fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x
  let rt : Base → ℝ := fun x ↦ rho x+t*b x
  have hrt : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rt := hr.add (contMDiff_const.mul hb)
  obtain ⟨hE0,hD0,h0⟩ := intrinsic_green_eigenfunction_test A hA hs hp rho hr hrp w f hw hf lam hef
  obtain ⟨_,_,hnew⟩ := intrinsic_green_eigenfunction_test At hAt hst hpt rt hrt hrpt f w hf hw lam hew
  have hEt := intrinsic_differential_pair_integrable At hAt hst hpt w f hw hf
  have hDt := sphereWeightedPairing_integrable rt w f hrt.continuous hw.continuous hf.continuous
  have hnew' : (∫ x, At x (sphereDifferential w x) (sphereDifferential f x) ∂sphereReferenceMeasure) =
      lam*sphereWeightedPairing rt w f := by
    rw [sphereWeightedPairing_symm rt w f,← hnew]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ hst x _ _))
  have heq (x : Base) : t*sphereEnergyDensity a b lam w f x =
      (At x (sphereDifferential w x) (sphereDifferential f x)-lam*(rt x*w x*f x)) -
      (A x (sphereDifferential w x) (sphereDifferential f x)-lam*(rho x*w x*f x)) := by
    change t*(a x*roundCotangentTensor x (sphereDifferential w x) (sphereDifferential f x)-
      lam*b x*w x*f x) =
      (A x (sphereDifferential w x) (sphereDifferential f x)+
        (t*a x)*roundCotangentTensor x (sphereDifferential w x) (sphereDifferential f x)-
        lam*((rho x+t*b x)*w x*f x)) -
      (A x (sphereDifferential w x) (sphereDifferential f x)-lam*(rho x*w x*f x))
    ring
  have hFt : Integrable (fun x ↦ At x (sphereDifferential w x) (sphereDifferential f x)-
      lam*(rt x*w x*f x)) sphereReferenceMeasure := hEt.sub (hDt.const_mul lam)
  have hF0 : Integrable (fun x ↦ A x (sphereDifferential w x) (sphereDifferential f x)-
      lam*(rho x*w x*f x)) sphereReferenceMeasure := hE0.sub (hD0.const_mul lam)
  have hzero : t*sphereEnergyForm a b lam w f = 0 := by
    rw [sphereEnergyForm,← integral_const_mul]
    simp_rw [heq]
    rw [integral_sub hFt hF0,
      integral_sub hEt (hDt.const_mul lam),integral_sub hE0 (hD0.const_mul lam),
      integral_const_mul,integral_const_mul,hnew',h0]
    change lam*sphereWeightedPairing rt w f-lam*sphereWeightedPairing rt w f-
      (lam*sphereWeightedPairing rho w f-lam*sphereWeightedPairing rho w f)=0
    ring
  exact (mul_eq_zero.mp hzero).resolve_left ht

end
end Yau.Target

end OAI
