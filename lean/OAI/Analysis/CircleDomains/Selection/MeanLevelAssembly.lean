import OAI.Analysis.CircleDomains.Topology.CountableClosedLevelCount
import OAI.Analysis.CircleDomains.Selection.FiniteFlagIntersections
import OAI.Analysis.CircleDomains.Selection.FiniteLevelAssembly

namespace OAI

/-! Measurable distinct-count inequalities let us interchange the path
and level parameters without a separate measurability assumption for
the free-incidence event.
-/

open Set Function Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem mean_parameter_level_count_le_of_no_free_hits
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (U Flags : Set X) (hU : IsSigmaCompact U) (hFlags : Flags.Countable)
    {Z : Type*} [MeasurableSpace Z] (μ : ProbabilityMeasure Z)
    (γmap : Z → C(PathTime, X)) (hγmap : Measurable γmap)
    (hfree : ∀ᵐ z ∂(μ : Measure Z), ∀ᵐ t : UnitAddCircle ∂volume,
      ¬ ∃ x ∈ range (γmap z) ∩ (Uᶜ \ Flags), (t, x) ∈ H) :
    (∫⁻ t : UnitAddCircle, ∫⁻ z, pathImageCount {x | (t, x) ∈ H} (γmap z) ∂(μ : Measure Z)) ≤
      (∫⁻ t : UnitAddCircle, ∫⁻ z, pathImageCount (U ∩ {x | (t, x) ∈ H}) (γmap z) ∂(μ : Measure Z)) +
      (∫⁻ t : UnitAddCircle, ∫⁻ z, pathImageCount (Flags ∩ {x | (t, x) ∈ H}) (γmap z) ∂(μ : Measure Z)) := by
  have hfull : Measurable (fun p : C(PathTime, X) × UnitAddCircle =>
      pathImageCount {x | (p.2, x) ∈ H} p.1) := by
    simpa only [exists_const, Prod.swap_prod_mk, mem_preimage] using
      (measurable_countable_closed_relation_path_count
        (H := fun _ : ℕ => Prod.swap ⁻¹' H) (fun _ => hH.preimage continuous_swap))
  have hdom : Measurable (fun p : C(PathTime, X) × UnitAddCircle =>
      pathImageCount (U ∩ {x | (p.2, x) ∈ H}) p.1) :=
    measurable_sigmaCompact_restricted_relation_path_count hU (hH.preimage continuous_swap)
  have hflag := measurable_flag_intersection_count hH Flags hFlags
  have hfullZ := hfull.comp (hγmap.prodMap (measurable_id (α := UnitAddCircle)))
  have hdomZ := hdom.comp (hγmap.prodMap (measurable_id (α := UnitAddCircle)))
  have hflagZ := hflag.comp (hγmap.prodMap (measurable_id (α := UnitAddCircle)))
  have hbound : ∀ᵐ z ∂(μ : Measure Z), ∀ᵐ t : UnitAddCircle ∂volume,
      pathImageCount {x | (t, x) ∈ H} (γmap z) ≤
        pathImageCount (U ∩ {x | (t, x) ∈ H}) (γmap z) +
        pathImageCount (Flags ∩ {x | (t, x) ∈ H}) (γmap z) := by
    filter_upwards [hfree] with z hz
    filter_upwards [hz] with t ht
    exact pathImageCount_level_le_of_no_free_hits U Flags _ (γmap z) ht
  have hmeas : MeasurableSet {p : Z × UnitAddCircle |
      pathImageCount {x | (p.2, x) ∈ H} (γmap p.1) ≤
        pathImageCount (U ∩ {x | (p.2, x) ∈ H}) (γmap p.1) +
        pathImageCount (Flags ∩ {x | (p.2, x) ∈ H}) (γmap p.1)} :=
    measurableSet_le hfullZ (hdomZ.add hflagZ)
  have hswap := (Measure.ae_ae_comm hmeas).mp hbound
  have hmeanD : Measurable (fun t : UnitAddCircle => ∫⁻ z,
      pathImageCount (U ∩ {x | (t, x) ∈ H}) (γmap z) ∂(μ : Measure Z)) :=
    (hdomZ.comp measurable_swap).lintegral_prod_right' (ν := (μ : Measure Z))
  rw [← lintegral_add_left hmeanD]
  apply lintegral_mono_ae
  filter_upwards [hswap] with t ht
  have hsection : Measurable (fun z : Z => pathImageCount (U ∩ {x | (t, x) ∈ H}) (γmap z)) :=
    hdomZ.comp (measurable_id.prodMk measurable_const)
  exact (lintegral_mono_ae ht).trans_eq
    (lintegral_add_left hsection (fun z => pathImageCount (Flags ∩ {x | (t, x) ∈ H}) (γmap z)))

end CircleDomainRigidity

end

end OAI
