import OAI.Analysis.CircleDomains.Topology.ClippedPaths

namespace OAI

/-! The arclength measure of a constant-extended path portion is exactly the
restriction of the original time measure. Thus adjacent portions add without
charging their shared endpoint. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem Ioc_timeClip (a b s t : PathTime) :
    Ioc (timeClip a b s) (timeClip a b t) = Ioc s t ∩ Ioc a b := by
  ext x
  simp only [timeClip, ContinuousMap.coe_mk, mem_Ioc, mem_inter_iff,
    max_lt_iff, min_lt_iff, le_max_iff, le_min_iff]
  constructor
  · rintro ⟨⟨hax, hmid⟩, hu⟩
    have hbt : x ≤ b ∧ x ≤ t := hu.resolve_left (not_le.mpr hax)
    have hs : s < x := hmid.resolve_left (not_lt.mpr hbt.1)
    exact ⟨⟨hs, hbt.2⟩, hax, hbt.1⟩
  · rintro ⟨⟨hs, ht⟩, ha, hb⟩
    exact ⟨⟨ha, Or.inr hs⟩, Or.inr ⟨hb, ht⟩⟩

variable {X : Type*} [MetricSpace X]

theorem pathLengthMeasure_clipped (γ : RectifiablePath X)
    {a b : PathTime} (hab : a ≤ b) :
    pathLengthMeasure (clippedPath γ hab) = (pathLengthMeasure γ).restrict (Icc a b) := by
  have heq : pathLengthMeasure (clippedPath γ hab) =
      (pathLengthMeasure γ).restrict (Ioc a b) := by
    apply Measure.ext_of_Ioc_finite
    · rw [pathLengthMeasure_clipped_univ γ hab, Measure.restrict_apply_univ,
        pathLengthMeasure_Icc γ hab, pathLengthMeasure_Ioc γ hab]
    · intro s t hst
      rw [pathLengthMeasure_clipped_Ioc γ hab hst.le,
        Measure.restrict_apply measurableSet_Ioc, Ioc_timeClip]
  exact heq.trans (Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := pathLengthMeasure γ)))

variable [MeasurableSpace X] [BorelSpace X]

def pathPortionOccupation (γ : RectifiablePath X) (a b : PathTime) : Measure X :=
  ((pathLengthMeasure γ).restrict (Icc a b)).map γ.val

omit [BorelSpace X] in
theorem pathOccupation_clipped (γ : RectifiablePath X) {a b : PathTime} (hab : a ≤ b) :
    pathOccupation (clippedPath γ hab) = pathPortionOccupation γ a b := by
  rw [pathOccupation, pathLengthMeasure_clipped γ hab]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change γ.val (max a (min b t)) = γ.val t
  rw [min_eq_right ht.2, max_eq_right ht.1]

omit [BorelSpace X] in
theorem pathPortionOccupation_congr (γ η : RectifiablePath X) {a b : PathTime}
    (hab : a ≤ b) (heq : EqOn γ.val η.val (Icc a b)) :
    pathPortionOccupation γ a b = pathPortionOccupation η a b := by
  rw [← pathOccupation_clipped γ hab, ← pathOccupation_clipped η hab]
  congr 1
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  apply heq
  rw [← range_timeClip hab]
  exact mem_range_self t

theorem pathPortionOccupation_add (γ : RectifiablePath X)
    {a b c : PathTime} (hab : a ≤ b) (hbc : b ≤ c) :
    pathPortionOccupation γ a c =
      pathPortionOccupation γ a b + pathPortionOccupation γ b c := by
  have hrestr : (pathLengthMeasure γ).restrict (Icc a c) =
      (pathLengthMeasure γ).restrict (Icc a b) + (pathLengthMeasure γ).restrict (Icc b c) := by
    have hdis : AEDisjoint (pathLengthMeasure γ) (Icc a b) (Icc b c) := by
      rw [AEDisjoint]
      have heq : Icc a b ∩ Icc b c = {b} := by
        ext x
        simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
        constructor
        · rintro ⟨⟨_, hxb⟩, hbx, _⟩
          exact le_antisymm hxb hbx
        · rintro rfl
          exact ⟨⟨hab, le_rfl⟩, le_rfl, hbc⟩
      rw [heq]
      exact measure_singleton b
    rw [← Icc_union_Icc_eq_Icc hab hbc]
    exact Measure.restrict_union₀ hdis measurableSet_Icc.nullMeasurableSet
  rw [pathPortionOccupation, hrestr, Measure.map_add]
  · rfl
  · exact γ.val.continuous.measurable

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_pathPortionOccupation (a b : PathTime) :
    Measurable (fun γ : RectifiablePath X => pathPortionOccupation γ a b) := by
  by_cases hab : a ≤ b
  · have hm : Measurable (fun γ : RectifiablePath X => pathOccupation (clippedPath γ hab)) :=
      measurable_pathOccupation.comp (continuous_clippedPath hab).measurable
    simpa only [pathOccupation_clipped _ hab] using hm
  · have heq : Icc a b = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge hab)
    simp only [pathPortionOccupation, heq, Measure.restrict_empty, Measure.map_zero]
    exact measurable_const

end CircleDomainRigidity

end

end OAI
