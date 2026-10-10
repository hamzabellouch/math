import OAI.Analysis.CircleDomains.Selection.MeanLevelAssembly
import OAI.Analysis.CircleDomains.Selection.FiniteFreeCount

namespace OAI

/-! Finite expected counts make the free-avoidance statement available
with the independent level chosen first. This uses Borel count inequalities
and does not assume measurability of the raw free-incidence event.
-/

open Set Function Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem ae_level_parameter_free_avoidance
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (U Flags : Set X) (hU : IsSigmaCompact U) (hFlags : Flags.Countable)
    (hdisj : Disjoint U Flags)
    {Z : Type*} [MeasurableSpace Z] (P : ProbabilityMeasure Z)
    (γmap : Z → C(PathTime, X)) (hγmap : Measurable γmap)
    (hfree : ∀ᵐ z ∂(P : Measure Z), ∀ᵐ t : UnitAddCircle ∂volume,
      ¬ ∃ x ∈ range (γmap z) ∩ (Uᶜ \ Flags), (t, x) ∈ H)
    (hmean : (∫⁻ t : UnitAddCircle, ∫⁻ z,
      pathImageCount {x | (t, x) ∈ H} (γmap z) ∂(P : Measure Z)) < ∞) :
    ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ z, pathImageCount {x | (t, x) ∈ H} (γmap z) ∂(P : Measure Z)) < ∞ ∧
      ∀ᵐ z ∂(P : Measure Z), ¬ ∃ x ∈ range (γmap z) ∩ (Uᶜ \ Flags), (t, x) ∈ H := by
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
  have hbound : ∀ᵐ z ∂(P : Measure Z), ∀ᵐ t : UnitAddCircle ∂volume,
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
  have hm : Measurable (fun t : UnitAddCircle => ∫⁻ z,
      pathImageCount {x | (t, x) ∈ H} (γmap z) ∂(P : Measure Z)) :=
    (hfullZ.comp measurable_swap).lintegral_prod_right' (ν := (P : Measure Z))
  filter_upwards [hswap, ae_lt_top hm hmean.ne] with t ht he
  refine ⟨he, ?_⟩
  have hsection : Measurable (fun z : Z => pathImageCount {x | (t, x) ∈ H} (γmap z)) :=
    hfullZ.comp (measurable_id.prodMk measurable_const)
  filter_upwards [ht, ae_lt_top hsection he.ne] with z hz hf
  exact no_free_hits_of_finite_count_le U Flags _ hdisj (γmap z) hf hz

end CircleDomainRigidity

end

end OAI
