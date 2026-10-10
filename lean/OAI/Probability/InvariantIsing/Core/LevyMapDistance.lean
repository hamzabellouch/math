import OAI.Probability.InvariantIsing.Spectral.CompactResolventTests

namespace OAI

/-! A direct coupling bound for the Levy--Prokhorov distance of two images. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
namespace InvariantIsing

theorem levyProkhorov_map_dist_le_ae {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (f g : Ω → E) (hf : Measurable f) (hg : Measurable g)
    {δ : ℝ} (hδ : 0 ≤ δ) (hfg : ∀ᵐ ω ∂P, dist (f ω) (g ω) ≤ δ) :
    levyProkhorovDist (P.map f) (P.map g) ≤ δ := by
  have : IsProbabilityMeasure (P.map f) := (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (P.map g) := (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).mpr inferInstance
  apply levyProkhorovDist_le_of_forall_le _ _ hδ
  intro ε S hε hS
  rw [Measure.map_apply hf hS,Measure.map_apply hg isOpen_thickening.measurableSet]
  have hs : f ⁻¹' S ≤ᵐ[P] g ⁻¹' thickening ε S := by
    filter_upwards [hfg] with ω hω hS'
    apply mem_thickening_iff.mpr
    exact ⟨f ω,hS',(by rw [dist_comm]; exact hω.trans_lt hε)⟩
  exact (measure_mono_ae hs).trans (le_add_right le_rfl)

end InvariantIsing

end

end OAI
