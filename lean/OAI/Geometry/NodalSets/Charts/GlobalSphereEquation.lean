import OAI.Geometry.NodalSets.Charts.IntrinsicLiftGeometry
import OAI.Geometry.NodalSets.Charts.SphereOperatorInvariance

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (lam : ℝ)
include hA hs hp hf

theorem intrinsic_global_equation_of_seed_exterior (K : Set Base)
    (hK : K ⊆ (extChartAt (𝓡 4) seedPoint).source)
    (hseed : ∀ x, -intrinsicWeightedChartOperator A rho f seedPoint (seedCoordEquiv x) =
      lam*f (seedSphereFromCoord x))
    (hext : ∀ p z, (extChartAt (𝓡 4) p).symm z ∉ K →
      -intrinsicWeightedChartOperator A rho f p z = lam*f ((extChartAt (𝓡 4) p).symm z)) :
    ∀ p z, -intrinsicWeightedChartOperator A rho f p z =
      lam*f ((extChartAt (𝓡 4) p).symm z) := by
  intro p z
  by_cases hz : (extChartAt (𝓡 4) p).symm z ∈ K
  · have hov : seedCoordEquiv.symm z ∈ sphereChartTransitionDomain p seedPoint := by
      simpa only [sphereChartTransitionDomain,sphereChartCoordMap,mem_preimage,
        seedCoordEquiv.apply_symm_apply] using hK hz
    have hi := intrinsicWeightedChartOperator_transition A hA hs hp f hf rho p seedPoint hov
    rw [seedCoordEquiv.apply_symm_apply] at hi
    rw [hi,hseed]
    have hpoint := sphereChartTransition_point p seedPoint hov
    simpa only [sphereChartCoordMap,seedSphereFromCoord,seedCoordEquiv.apply_symm_apply] using
      congrArg (fun y ↦ lam*f y) hpoint
  · exact hext p z hz

omit hA hs hp hf in
lemma intrinsic_global_equation_at_center
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho f p z =
      lam*f ((extChartAt (𝓡 4) p).symm z)) :
    ∀ x : Base, -intrinsicWeightedChartOperator A rho f x (extChartAt (𝓡 4) x x) = lam*f x := by
  intro x
  simpa only [(extChartAt (𝓡 4) x).left_inv (mem_extChartAt_source x)] using he x (extChartAt (𝓡 4) x x)

theorem intrinsic_lift_of_seed_exterior
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (hf0 : f ≠ 0) (K : Set Base) (hK : K ⊆ (extChartAt (𝓡 4) seedPoint).source)
    (hseed : ∀ x, -intrinsicWeightedChartOperator A rho f seedPoint (seedCoordEquiv x) =
      lam*f (seedSphereFromCoord x))
    (hext : ∀ p z, (extChartAt (𝓡 4) p).symm z ∉ K →
      -intrinsicWeightedChartOperator A rho f p z = lam*f ((extChartAt (𝓡 4) p).symm z)) :
    ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift f) ∧ circleLift f ≠ 0 ∧
      ∀ x : Manifold5, -chartLaplacian (intrinsicWeightedMetric A hA hs hp rho hr hrp)
        (extChartAt modelWithCorners x) (circleLift f) (extChartAt modelWithCorners x x) =
          lam*circleLift f x := by
  apply intrinsicWeightedMetric_eigenfunction A hA hs hp rho hr hrp f hf hf0 lam
  exact intrinsic_global_equation_at_center A rho f lam
    (intrinsic_global_equation_of_seed_exterior A hA hs hp rho f hf lam K hK hseed hext)

end
end Yau.Target

end OAI
