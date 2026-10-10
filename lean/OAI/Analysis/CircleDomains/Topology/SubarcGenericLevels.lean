import OAI.Analysis.CircleDomains.Topology.SubarcIntersectionCount
import OAI.Analysis.CircleDomains.Probability.LevelLawQuantifiers

namespace OAI

/-! Generic prior levels survive measurable subarc selection and the
factor-two compact conditioning used for terminal arc laws. The free set
need not be measurable: finite Borel count inequalities carry the statement. -/

open Set Function Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem subarc_generic_levels
    (μ η : ProbabilityMeasure C(PathTime, X))
    (f : C(PathTime, X) → C(PathTime, X))
    (hf : AEMeasurable f (μ : Measure C(PathTime, X)))
    (hs : ∀ᵐ γ : C(PathTime, X) ∂(μ : Measure C(PathTime, X)), range (f γ) ⊆ range γ)
    (hη : (η : Measure C(PathTime, X)) ≤
      (2 : ℝ≥0∞) • (μ.map f : Measure C(PathTime, X)))
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (U Flags : Set X) (hU : IsSigmaCompact U) (hFlags : Flags.Countable)
    (hdisj : Disjoint U Flags)
    (hgeneric : ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (t, x) ∈ H} γ ∂(μ : Measure C(PathTime, X))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, X) ∂(μ : Measure C(PathTime, X)),
        ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), (t, x) ∈ H) :
    ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ α, pathImageCount {x | (t, x) ∈ H} α ∂(η : Measure C(PathTime, X))) < ∞ ∧
      ∀ᵐ α : C(PathTime, X) ∂(η : Measure C(PathTime, X)),
        ¬ ∃ x ∈ range α ∩ (Uᶜ \ Flags), (t, x) ∈ H := by
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
  have hclosed : IsClosed {x | (t, x) ∈ H} :=
    hH.preimage (continuous_const.prodMk continuous_id)
  have hm := hfull.comp (measurable_id.prodMk (measurable_const (a := t)))
  have hd := hdom.comp (measurable_id.prodMk (measurable_const (a := t)))
  have hb := hflag.comp (measurable_id.prodMk (measurable_const (a := t)))
  have hp : MeasurableSet {α : C(PathTime, X) |
      pathImageCount {x | (t, x) ∈ H} α < ∞ ∧
      pathImageCount {x | (t, x) ∈ H} α ≤
        pathImageCount (U ∩ {x | (t, x) ∈ H}) α +
        pathImageCount (Flags ∩ {x | (t, x) ∈ H}) α} :=
    (measurableSet_lt hm measurable_const).inter (measurableSet_le hm (hd.add hb))
  have hselected : ∀ᵐ γ : C(PathTime, X) ∂(μ : Measure C(PathTime, X)),
      pathImageCount {x | (t, x) ∈ H} (f γ) < ∞ ∧
      pathImageCount {x | (t, x) ∈ H} (f γ) ≤
        pathImageCount (U ∩ {x | (t, x) ∈ H}) (f γ) +
        pathImageCount (Flags ∩ {x | (t, x) ∈ H}) (f γ) := by
    filter_upwards [hs, ht.2, ae_lt_top hm ht.1.ne] with γ hsub hfree hfin
    have hfree' : ¬ ∃ x ∈ range (f γ) ∩ (Uᶜ \ Flags), (t, x) ∈ H := by
      rintro ⟨x, ⟨hx, hxf⟩, hxH⟩
      exact hfree ⟨x, ⟨hsub hx, hxf⟩, hxH⟩
    exact ⟨(pathImageCount_mono_range _ hsub).trans_lt hfin,
      pathImageCount_level_le_of_no_free_hits U Flags _ (f γ) hfree'⟩
  have hmap : ∀ᵐ α : C(PathTime, X) ∂(μ.map f : Measure C(PathTime, X)),
      pathImageCount {x | (t, x) ∈ H} α < ∞ ∧
      pathImageCount {x | (t, x) ∈ H} α ≤
        pathImageCount (U ∩ {x | (t, x) ∈ H}) α +
        pathImageCount (Flags ∩ {x | (t, x) ∈ H}) α := by
    rw [ProbabilityMeasure.toMeasure_map]
    exact (ae_map_iff hf hp).mpr hselected
  refine ⟨finite_mean_subarc_intersections μ η f hf hs hη hclosed ht.1, ?_⟩
  filter_upwards [(Measure.absolutelyContinuous_of_le_smul hη).ae_le hmap] with α hα
  exact no_free_hits_of_finite_count_le U Flags _ hdisj α hα.1 hα.2

theorem IsSubarcLawReduction.generic_levels
    {μ η : ProbabilityMeasure C(PathTime, X)} (hred : IsSubarcLawReduction μ η)
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (U Flags : Set X) (hU : IsSigmaCompact U) (hFlags : Flags.Countable)
    (hdisj : Disjoint U Flags)
    (hgeneric : ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (t, x) ∈ H} γ ∂(μ : Measure C(PathTime, X))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, X) ∂(μ : Measure C(PathTime, X)),
        ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), (t, x) ∈ H) :
    ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ α, pathImageCount {x | (t, x) ∈ H} α ∂(η : Measure C(PathTime, X))) < ∞ ∧
      ∀ᵐ α : C(PathTime, X) ∂(η : Measure C(PathTime, X)),
        ¬ ∃ x ∈ range α ∩ (Uᶜ \ Flags), (t, x) ∈ H := by
  obtain ⟨f, hf, hs, hη⟩ := hred
  exact subarc_generic_levels μ η f hf hs hη hH U Flags hU hFlags hdisj hgeneric

end CircleDomainRigidity

end

end OAI
