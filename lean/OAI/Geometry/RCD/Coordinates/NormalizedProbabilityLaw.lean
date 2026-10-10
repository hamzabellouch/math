import OAI.Geometry.RCD.Sobolev.MeasuredTestScaling
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace OAI

/-! # Normalized finite laws and their exact test integrals -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] [Nonempty X]

def normalizedProbabilityLaw (μ : Measure X) [IsFiniteMeasure μ] : ProbabilityMeasure X :=
  MeasureTheory.FiniteMeasure.normalize (⟨μ,inferInstance⟩ : MeasureTheory.FiniteMeasure X)

theorem normalizedProbabilityLaw_integral (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ≠0) (f : X → ℝ) :
    (∫ x, f x ∂(normalizedProbabilityLaw μ : Measure X))=
      (μ.real univ)⁻¹*(∫ x, f x ∂μ) := by
  have hfinite : (⟨μ,inferInstance⟩ : MeasureTheory.FiniteMeasure X)≠
      (⟨0,MeasureTheory.isFiniteMeasureZero⟩ : MeasureTheory.FiniteMeasure X) := by
    intro he
    exact hμ (congrArg MeasureTheory.FiniteMeasure.toMeasure he)
  have h := MeasureTheory.FiniteMeasure.average_eq_integral_normalize
    (⟨μ,inferInstance⟩ : MeasureTheory.FiniteMeasure X) hfinite f
  simpa only [average_eq,smul_eq_mul,normalizedProbabilityLaw,
    MeasureTheory.FiniteMeasure.toMeasure_mk] using h.symm

theorem normalizedProbabilityLaw_map_integral {Y : Type*} [MeasurableSpace Y]
    [TopologicalSpace Y] [OpensMeasurableSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ≠0) {v : X → Y} (hv : Measurable v)
    {f : Y → ℝ} (hf : Continuous f) :
    (∫ y, f y ∂((normalizedProbabilityLaw μ).map v : Measure Y))=
      (μ.real univ)⁻¹*(∫ x, f (v x) ∂μ) := by
  rw [ProbabilityMeasure.toMeasure_map,integral_map hv.aemeasurable hf.aestronglyMeasurable]
  exact normalizedProbabilityLaw_integral μ hμ (f ∘ v)

theorem normalizedProbabilityLaw_real (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ≠0) {s : Set X} (hs : MeasurableSet s) :
    (normalizedProbabilityLaw μ : Measure X).real s=(μ.real univ)⁻¹*μ.real s := by
  simpa only [integral_indicator hs,setIntegral_const,smul_eq_mul,mul_one] using
    normalizedProbabilityLaw_integral μ hμ (s.indicator (fun _ => (1:ℝ)))

end RegularPointCoordinates

end

end OAI
