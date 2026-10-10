import OAI.Geometry.NodalSets.Charts.IntrinsicDifferentialPairChart
import OAI.Geometry.NodalSets.Charts.SphereReferenceMeasureFinite
import OAI.Geometry.NodalSets.Charts.SphereSmoothFromCharts

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

lemma intrinsic_differential_pair_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) :
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x (sphereDifferential u x) (sphereDifferential v x)) :=
  sphere_smooth_of_chart_pullbacks _ (intrinsic_differential_pair_pullback_smooth A hA hs hp u v hu hv)

lemma intrinsic_differential_pair_integrable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) :
    Integrable (fun x ↦ A x (sphereDifferential u x) (sphereDifferential v x)) sphereReferenceMeasure :=
  sphereReferenceMeasure_integrable_continuous _
    (intrinsic_differential_pair_smooth A hA hs hp u v hu hv).continuous

end
end Yau.Target

end OAI
