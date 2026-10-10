import OAI.Analysis.CircleDomains.Selection.TranslatedRayOrder

namespace OAI

/-! The right components of integer translates form a decreasing family.
This is derived from crosscut separation and the order of the actual starts. -/

open Set Function Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem HalfPlaneRay.boundary_right (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ}
    (hH : R.IsJordan H) {x : ℝ} (hx : (R.curve ⟨0, bot_lt_top⟩).re < x) :
    halfPlaneDisk x ∉ closure (jordanInterior H) := by
  have hm : halfPlaneDisk x ∉ range R.crosscut := by
    rw [R.boundary_hit_iff]
    exact ne_of_gt hx
  have hb := R.side_boundary hH x hm
  change (if halfPlaneDisk x ∈ closure (jordanInterior H) then false else true) = _ at hb
  rw [ite_eq_right (not_le_of_gt hx)] at hb
  intro hi
  rw [ite_eq_left hi] at hb
  cases hb

 theorem earlier_crosscut_in_later_filling (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) {k l : ℤ} (hkl : k < l)
    (H : ℂ ≃ₜ ℂ) (hH : (translatedHalfPlaneRay γ hγ l).IsJordan H) :
    range (translatedHalfPlaneRay γ hγ k).crosscut ⊆ closure (jordanInterior H) := by
  rintro z ⟨t, rfl⟩
  by_cases ht : t < ⊤
  · change (translatedHalfPlaneRay γ hγ k).compactify t ∈ _
    rw [HalfPlaneRay.compactify, dite_eq_left ht]
    exact earlier_ray_left γ hγ hkl H hH ⟨t, ht⟩
  · have he : t = ⊤ := top_le_iff.mp (not_lt.mp ht)
    subst t
    have hf : (1 : ℂ) ∈ frontier (jordanInterior H) := by
      rw [hH]
      left
      exact ⟨⊤, (translatedHalfPlaneRay γ hγ l).compactify_top⟩
    change (translatedHalfPlaneRay γ hγ k).compactify ⊤ ∈ _
    rw [HalfPlaneRay.compactify_top]
    exact frontier_subset_closure hf

 theorem translated_rightSide_antitone (hsep : UnitDiskCrosscutSeparation)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    {k l : ℤ} (hkl : k < l) (Hk Hl : ℂ ≃ₜ ℂ)
    (hk : (translatedHalfPlaneRay γ hγ k).IsJordan Hk)
    (hl : (translatedHalfPlaneRay γ hγ l).IsJordan Hl) :
    Metric.closedBall 0 1 \ closure (jordanInterior Hl) ⊆
      Metric.closedBall 0 1 \ closure (jordanInterior Hk) := by
  let R := translatedHalfPlaneRay γ hγ k
  let S := translatedHalfPlaneRay γ hγ l
  let A := Metric.closedBall (0 : ℂ) 1 \ closure (jordanInterior Hl)
  have havoid : ∀ z : A, z.val ∉ range R.crosscut := by
    intro z hz
    exact z.property.2 (earlier_crosscut_in_later_filling γ hγ hkl Hl hl hz)
  let f : A → R.CutDomain := fun z => ⟨z.val, z.property.1, havoid z⟩
  have hc : Continuous f := continuous_subtype_val.subtype_mk _
  let : PreconnectedSpace A := Subtype.preconnectedSpace
    (S.rightSide_connected hsep Hl hl).isPreconnected
  let x : ℝ := max (R.curve ⟨0, bot_lt_top⟩).re (S.curve ⟨0, bot_lt_top⟩).re + 1
  have hkx : (R.curve ⟨0, bot_lt_top⟩).re < x := by
    exact lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one
  have hlx : (S.curve ⟨0, bot_lt_top⟩).re < x := by
    exact lt_add_of_le_of_pos (le_max_right _ _) zero_lt_one
  let z₀ : A := ⟨halfPlaneDisk x, Metric.mem_closedBall.mpr
    (by simpa only [dist_zero_right] using (cayleyBoundary_norm x).le), S.boundary_right hl hlx⟩
  intro z hz
  let w : A := ⟨z, hz⟩
  have he := ((R.isLocallyConstant_side hk).comp_continuous hc).apply_eq_of_preconnectedSpace w z₀
  have he' : (if z ∈ closure (jordanInterior Hk) then false else true) = true := by
    simpa only [Function.comp_apply, HalfPlaneRay.side, f, w, z₀,
      ite_eq_right (R.boundary_right hk hkx)] using he
  refine ⟨hz.1, ?_⟩
  intro hi
  rw [ite_eq_left hi] at he'
  cases he'

 theorem rayRightIndices_downward (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im)
    {k l : ℤ} (hkl : k ≤ l) (hl : l ∈ rayRightIndices hsch γ hγ z) :
    k ∈ rayRightIndices hsch γ hγ z := by
  rcases hkl.eq_or_lt with rfl | hlt
  · exact hl
  · exact (translated_rightSide_antitone hsep γ hγ hlt
      (rayJordan hsch γ hγ k) (rayJordan hsch γ hγ l)
      (rayJordan_spec hsch γ hγ k) (rayJordan_spec hsch γ hγ l)
      ⟨Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le hz), hl⟩).2

 theorem mem_rayRightIndices_iff_le (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im) (k : ℤ) :
    k ∈ rayRightIndices hsch γ hγ z ↔ k ≤ geometricRayIndex hsch γ hγ z := by
  have hg := geometricRayIndex_isGreatest hsch γ hγ z hz
  exact ⟨fun hk => hg.2 hk, fun hk => rayRightIndices_downward hsch hsep γ hγ z hz hk hg.1⟩

end CircleDomainRigidity

end

end OAI
