import OAI.Analysis.IrrationalRotation.Model.ProductSampling
import OAI.Analysis.IrrationalRotation.Analysis.SubmeasureLpDensity

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.ProductModel

theorem samplingMeasure_isFinite_of_uniformL2
    {η : ℕ → Measure EndpointPair} (hη : HasUniformL2Marginals η) (l : ℕ) :
    IsFiniteMeasure (η l) := by
  obtain ⟨H, hH, hdensity⟩ := hη
  obtain ⟨f, g, hf0, hg0, hfst, hsnd, hfH, hgH⟩ := hdensity l
  have hfint : Integrable f baseMeasure := (Lp.memLp f).integrable (by norm_num)
  have : IsFiniteMeasure
      (baseMeasure.withDensity (fun x => ENNReal.ofReal (f x))) :=
    isFiniteMeasure_withDensity
      ((lintegral_ofReal_ne_top_iff_integrable hfint.aestronglyMeasurable hf0).2 hfint)
  have : IsFiniteMeasure ((η l).map Prod.fst) := hfst ▸ inferInstance
  exact Measure.isFiniteMeasure_of_map measurable_fst.aemeasurable

theorem uniformL2Marginals_of_domination
    {η ξ : ℕ → Measure EndpointPair}
    (hη : HasUniformL2Marginals η) (hfinite : ∀ l, IsFiniteMeasure (η l))
    (hle : ∀ l, ξ l ≤ η l) : HasUniformL2Marginals ξ := by
  obtain ⟨H, hH, hdensity⟩ := hη
  refine ⟨H, hH, ?_⟩
  intro l
  have : IsFiniteMeasure (η l) := hfinite l
  have : IsFiniteMeasure (ξ l) := isFiniteMeasure_of_le (η l) (hle l)
  obtain ⟨f, g, hf0, hg0, hfst, hsnd, hfH, hgH⟩ := hdensity l
  have hfirst : (ξ l).map Prod.fst ≤
      baseMeasure.withDensity (fun x => ENNReal.ofReal (f x)) := by
    rw [← hfst]
    exact Measure.map_mono (hle l) measurable_fst
  have hsecond : (ξ l).map Prod.snd ≤
      baseMeasure.withDensity (fun x => ENNReal.ofReal (g x)) := by
    rw [← hsnd]
    exact Measure.map_mono (hle l) measurable_snd
  obtain ⟨f', hf'0, _, hf'map, hf'norm⟩ :=
    SubmeasureDensity.exists_lp_density_of_le_withDensity f hf0 hfirst
  obtain ⟨g', hg'0, _, hg'map, hg'norm⟩ :=
    SubmeasureDensity.exists_lp_density_of_le_withDensity g hg0 hsecond
  exact ⟨f', g', hf'0, hg'0, hf'map, hg'map,
    hf'norm.trans hfH, hg'norm.trans hgH⟩

theorem uniformL2Marginals_restrict_with_finiteness
    {η : ℕ → Measure EndpointPair}
    (hη : HasUniformL2Marginals η) (hfinite : ∀ l, IsFiniteMeasure (η l))
    (s : ℕ → Set EndpointPair) :
    HasUniformL2Marginals (fun l => (η l).restrict (s l)) :=
  uniformL2Marginals_of_domination hη hfinite (fun _ => Measure.restrict_le_self)

theorem uniformL2Marginals_of_domination_auto
    {η ξ : ℕ → Measure EndpointPair}
    (hη : HasUniformL2Marginals η) (hle : ∀ l, ξ l ≤ η l) :
    HasUniformL2Marginals ξ :=
  uniformL2Marginals_of_domination hη (samplingMeasure_isFinite_of_uniformL2 hη) hle

theorem uniformL2Marginals_restrict
    {η : ℕ → Measure EndpointPair}
    (hη : HasUniformL2Marginals η) (s : ℕ → Set EndpointPair) :
    HasUniformL2Marginals (fun l => (η l).restrict (s l)) :=
  uniformL2Marginals_of_domination_auto hη (fun _ => Measure.restrict_le_self)

theorem positiveOrderedOrbitSupport_of_domination
    {θ : ℕ → ℝ} {η ξ : Measure EndpointPair}
    (hη : SupportedOnPositiveOrderedOrbitPairs θ η) (hle : ξ ≤ η) :
    SupportedOnPositiveOrderedOrbitPairs θ ξ := by
  obtain ⟨N, hN, hsupport⟩ := hη
  exact ⟨N, hN, ae_mono hle hsupport⟩

end Invariant233.ProductModel

end

end OAI
