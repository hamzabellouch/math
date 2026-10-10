import OAI.Analysis.CircleDomains.Probability.LevelLawQuantifiers
import OAI.Analysis.CircleDomains.Probability.SupportedProbability

namespace OAI

/-! Passing the level-first estimates between a coded probability law,
its actual path law, and a supported subtype law. -/

open Set Function Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem map_generic_levels
    {Z : Type*} [MeasurableSpace Z] (P : ProbabilityMeasure Z)
    (γmap : Z → C(PathTime, X)) (hγmap : Measurable γmap)
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (U Flags : Set X) (hU : IsSigmaCompact U) (hFlags : Flags.Countable)
    (hdisj : Disjoint U Flags)
    (hgeneric : ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ z, pathImageCount {x | (t, x) ∈ H} (γmap z) ∂(P : Measure Z)) < ∞ ∧
      ∀ᵐ z ∂(P : Measure Z),
        ¬ ∃ x ∈ range (γmap z) ∩ (Uᶜ \ Flags), (t, x) ∈ H) :
    ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (t, x) ∈ H} γ
        ∂(P.map γmap : Measure C(PathTime, X))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, X) ∂(P.map γmap : Measure C(PathTime, X)),
        ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), (t, x) ∈ H := by
  have hfull : Measurable (fun p : C(PathTime, X) × UnitAddCircle =>
      pathImageCount {x | (p.2, x) ∈ H} p.1) := by
    simpa only [exists_const, Prod.swap_prod_mk, mem_preimage] using
      (measurable_countable_closed_relation_path_count
        (H := fun _ : ℕ => Prod.swap ⁻¹' H) (fun _ => hH.preimage continuous_swap))
  have hdom : Measurable (fun p : C(PathTime, X) × UnitAddCircle =>
      pathImageCount (U ∩ {x | (p.2, x) ∈ H}) p.1) :=
    measurable_sigmaCompact_restricted_relation_path_count hU (hH.preimage continuous_swap)
  have hflag := measurable_flag_intersection_count hH Flags hFlags
  filter_upwards [hgeneric] with t ht
  have hm : Measurable (fun γ : C(PathTime, X) => pathImageCount {x | (t, x) ∈ H} γ) :=
    hfull.comp (measurable_id.prodMk (measurable_const (a := t)))
  have hd := hdom.comp (measurable_id.prodMk (measurable_const (a := t)))
  have hb := hflag.comp (measurable_id.prodMk (measurable_const (a := t)))
  have hp : MeasurableSet {γ : C(PathTime, X) |
      pathImageCount {x | (t, x) ∈ H} γ < ∞ ∧
      pathImageCount {x | (t, x) ∈ H} γ ≤
        pathImageCount (U ∩ {x | (t, x) ∈ H}) γ +
        pathImageCount (Flags ∩ {x | (t, x) ∈ H}) γ} :=
    (measurableSet_lt hm measurable_const).inter (measurableSet_le hm (hd.add hb))
  have hsource : ∀ᵐ z ∂(P : Measure Z),
      pathImageCount {x | (t, x) ∈ H} (γmap z) < ∞ ∧
      pathImageCount {x | (t, x) ∈ H} (γmap z) ≤
        pathImageCount (U ∩ {x | (t, x) ∈ H}) (γmap z) +
        pathImageCount (Flags ∩ {x | (t, x) ∈ H}) (γmap z) := by
    filter_upwards [ht.2, ae_lt_top (hm.comp hγmap) ht.1.ne] with z hz hfin
    exact ⟨hfin, pathImageCount_level_le_of_no_free_hits U Flags _ (γmap z) hz⟩
  have hmap : ∀ᵐ γ : C(PathTime, X) ∂(P.map γmap : Measure C(PathTime, X)),
      pathImageCount {x | (t, x) ∈ H} γ < ∞ ∧
      pathImageCount {x | (t, x) ∈ H} γ ≤
        pathImageCount (U ∩ {x | (t, x) ∈ H}) γ +
        pathImageCount (Flags ∩ {x | (t, x) ∈ H}) γ := by
    rw [ProbabilityMeasure.toMeasure_map]
    exact (ae_map_iff hγmap.aemeasurable hp).mpr hsource
  refine ⟨?_, hmap.mono fun γ hγ =>
    no_free_hits_of_finite_count_le U Flags _ hdisj γ hγ.1 hγ.2⟩
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map' hm.aemeasurable hγmap.aemeasurable]
  exact ht.1

omit [BorelSpace C(PathTime, X)] in
theorem supportedProbability_generic_levels
    (μ : ProbabilityMeasure C(PathTime, X)) (A : Set C(PathTime, X))
    (hA : MeasurableSet A) (hmem : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), γ ∈ A)
    (H : Set (UnitAddCircle × X)) (Free : Set X)
    (hgeneric : ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (t, x) ∈ H} γ ∂(μ : Measure C(PathTime, X))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, X) ∂(μ : Measure C(PathTime, X)),
        ¬ ∃ x ∈ range γ ∩ Free, (t, x) ∈ H) :
    ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (t, x) ∈ H} γ
        ∂((supportedProbability μ A hA hmem).map Subtype.val : Measure C(PathTime, X))) < ∞ ∧
      ∀ᵐ γ : A ∂(supportedProbability μ A hA hmem : Measure A),
        ¬ ∃ x ∈ range γ.val ∩ Free, (t, x) ∈ H := by
  filter_upwards [hgeneric] with t ht
  refine ⟨by simpa only [supportedProbability_map] using ht.1, ?_⟩
  have hm := ht.2
  rw [← supportedProbability_map μ A hA hmem, ProbabilityMeasure.toMeasure_map] at hm
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable hm

end CircleDomainRigidity

end

end OAI
