import OAI.Geometry.NodalSets.Charts.SphereFiniteSmoothPartition
import OAI.Geometry.NodalSets.Charts.SphereReferenceMeasurePositive
import OAI.Geometry.NodalSets.Elliptic.IntrinsicCompactWeakEquation
import OAI.Geometry.NodalSets.Elliptic.IntrinsicEnergyFiniteSum

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

lemma intrinsic_green_compact_chart_test (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hrp : ∀ x, 0 < rho x)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho v p z =
      lam*v ((extChartAt (𝓡 4) p).symm z))
    (p : Base) (hc : HasCompactSupport (u ∘ sphereChartCoordMap p)) :
    (∫ x, A x (sphereDifferential u x) (sphereDifferential v x) ∂sphereReferenceMeasure) =
      lam*sphereWeightedPairing rho u v := by
  have hw := (intrinsic_compact_weak_equation A hA hs hp rho hrp v hv lam he p
    (u ∘ sphereChartCoordMap p) (spherePullback_smooth u hu p) hc).2.2
  rw [sphereReferenceMeasure_integral_chart p,sphereWeightedPairing,
    sphereReferenceMeasure_integral_chart p,← integral_const_mul]
  simp only [roundChartDensity_coord_eq,intrinsic_differential_pair_chart A u v hu hv]
  rw [hw]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ by
    simp only [Function.comp_apply,intrinsicRealPotential]
    ring)

theorem intrinsic_green_eigenfunction_test (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho v p z =
      lam*v ((extChartAt (𝓡 4) p).symm z)) :
    Integrable (fun x ↦ A x (sphereDifferential u x) (sphereDifferential v x)) sphereReferenceMeasure ∧
    Integrable (fun x ↦ rho x*u x*v x) sphereReferenceMeasure ∧
    (∫ x, A x (sphereDifferential u x) (sphereDifferential v x) ∂sphereReferenceMeasure) =
      lam*sphereWeightedPairing rho u v := by
  classical
  refine ⟨intrinsic_differential_pair_integrable A hA hs hp u v hu hv,
    sphereWeightedPairing_integrable rho u v hr.continuous hu.continuous hv.continuous,?_⟩
  obtain ⟨P,theta,htheta,_,hsum,_,_,hcompact⟩ := sphere_finite_smooth_partition
  let f : {p // p ∈ P} → Base → ℝ := fun p x ↦ theta p x*u x
  have hf (p : {p // p ∈ P}) : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (f p) := (htheta p).mul hu
  have hsumf (x : Base) : ∑ p, f p x = u x := by
    simp only [f,← Finset.sum_mul,hsum,one_mul]
  have hlocal (p : {p // p ∈ P}) := intrinsic_green_compact_chart_test A hA hs hp rho hrp
    (f p) v (hf p) hv lam he p.val ((hcompact p).mul_right)
  calc
    _ = ∫ x, ∑ p, A x (sphereDifferential (f p) x) (sphereDifferential v x) ∂sphereReferenceMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ (sphere_differential_pair_finite_sum A f u v hf hu hv hsumf x).symm)
    _ = ∑ p, ∫ x, A x (sphereDifferential (f p) x) (sphereDifferential v x) ∂sphereReferenceMeasure :=
      integral_finsetSum _ (fun p _ ↦ intrinsic_differential_pair_integrable A hA hs hp (f p) v (hf p) hv)
    _ = lam*(∑ p, sphereWeightedPairing rho (f p) v) := by simp only [hlocal,Finset.mul_sum]
    _ = lam*sphereWeightedPairing rho u v := by
      congr 1
      unfold sphereWeightedPairing
      rw [← integral_finsetSum _ (fun p _ ↦ sphereWeightedPairing_integrable rho (f p) v
        hr.continuous (hf p).continuous hv.continuous)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ by
        change (∑ p, rho x*f p x*v x) = rho x*u x*v x
        rw [← Finset.sum_mul,← Finset.mul_sum,hsumf])

end
end Yau.Target

end OAI
