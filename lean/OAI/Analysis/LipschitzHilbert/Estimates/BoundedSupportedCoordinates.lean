import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedSymbolForm

namespace OAI

/-! Coordinate integrability follows from the vector indicator bound,
without a factor depending on the number of coordinates. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem bounded_supported_coordinate_integrable {κ : Type} [Fintype κ]
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hbound : ∀ z, ‖g z‖≤1)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (hEfin : planeMeasure E≠∞)
    (hsupport : ∀ z, z∉E → g z=0) (k : κ) : Integrable (fun z => g z k) planeMeasure := by
  have hI : Integrable (E.indicator (fun _ => (1:ℝ))) planeMeasure :=
    (integrable_indicator_iff hE).2 (integrableOn_const (μ:=planeMeasure) hEfin)
  have hm : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  apply hI.mono' hm.aestronglyMeasurable
  filter_upwards [] with z
  by_cases hz : z∈E
  · simpa only [Set.indicator_of_mem hz] using (PiLp.norm_apply_le (g z) k).trans (hbound z)
  · simp only [Set.indicator_of_notMem hz,hsupport z hz,WithLp.ofLp_zero,Pi.zero_apply,norm_zero,le_refl]

end LipschitzHilbert.PacketRepresentation

end

end OAI
