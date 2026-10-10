import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Hermitian

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)

lemma correctedDdc_norm_off_source {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f)
    (p : X) {y : Space} (hy : y ∈ (extChartAt Model p).target)
    (hx : (extChartAt Model p).symm y ∉ tsupport f) (v : Space) :
    ‖ManifoldForms.pullback (correctedDdc A J α hs ht H Gs hf).val
      (extChartAt Model p).symm y ![v,coordinateJ J p y v]‖ =
      ‖nonharmonicCorrectionLM A J α hs ht Gs p y
        (smoothAntiProjection A J α hs ht (smoothDdc J hf)) ![v,coordinateJ J p y v]‖ := by
  rw [correctedDdc_pullback_complexLine A J α hs ht H Gs hf p hy]
  have he : ManifoldForms.pullback (exteriorDerivative (complexDifferential J f))
        (extChartAt Model p).symm y ![v,coordinateJ J p y v] = 0 := by
    change exteriorDerivative (complexDifferential J f) ((extChartAt Model p).symm y) _ = 0
    rw [ddc_zero_off J hx]
    rfl
  rw [he,zero_sub,norm_neg]
end TamingCompatibility.GeometricHilbert

end

end OAI
