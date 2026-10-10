import Mathlib
import OAI.Geometry.PrescribedPotential.AnalyticSupport
import OAI.Geometry.PrescribedRicci.MongeAmpereEnergy

namespace OAI

/-! Kahler Volume Measure. -/

section

 
noncomputable section
open Matrix Filter Set Topology MeasureTheory
open scoped ContDiff ComplexOrder Classical CompactlySupported
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X}
namespace KaehlerMetric

def integralPositive (g : KaehlerMetric A) : C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toFun f := g.integral f
  map_add' f h := g.integral_add f.continuous h.continuous
  map_smul' c f := g.integral_const_mul c f
  monotone' f h hfh := g.integral_mono f.continuous h.continuous hfh

variable [MeasurableSpace X] [BorelSpace X]

def volumeMeasure (g : KaehlerMetric A) : Measure X :=
  RealRMK.rieszMeasure g.integralPositive

instance volumeMeasure_regular (g : KaehlerMetric A) : g.volumeMeasure.Regular := by
  dsimp [volumeMeasure]
  infer_instance

instance volumeMeasure_finite (g : KaehlerMetric A) : IsFiniteMeasure g.volumeMeasure := by
  dsimp [volumeMeasure]
  infer_instance

lemma integral_volumeMeasure (g : KaehlerMetric A) {f : X → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂g.volumeMeasure = g.integral f := by
  exact RealRMK.integral_rieszMeasure g.integralPositive
    ⟨⟨f, hf⟩, HasCompactSupport.of_compactSpace f⟩

end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI
