import OAI.Analysis.CircleDomains.Topology.CutPathComponents
import OAI.Analysis.CircleDomains.Selection.TranslatedSideNesting

namespace OAI

/-! Side membership is characterized by a path avoiding the crosscut to
the corresponding explicit real-boundary point. -/

open Set Function Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def DiskAvoidingPath (p : C(PathTime, ℂ)) (z w : ℂ) : Prop :=
  ∃ δ : C(PathTime, ℂ), δ 0 = z ∧ δ 1 = w ∧
    ∀ t, δ t ∈ Metric.closedBall 0 1 \ range p

namespace HalfPlaneRay

theorem side_eq_iff_avoidingPath (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) (x y : R.CutDomain) :
    R.side H x = R.side H y ↔ DiskAvoidingPath R.crosscut.toContinuousMap x.val y.val := by
  constructor
  · intro h
    have hj := (R.side_eq_iff_joined hsep hH x y).mp h
    let p := hj.somePath
    refine ⟨⟨fun t => (p t).val, continuous_subtype_val.comp p.continuous⟩, ?_, ?_, ?_⟩
    · exact congrArg Subtype.val p.source
    · exact congrArg Subtype.val p.target
    · exact fun t => (p t).property
  · rintro ⟨δ, h0, h1, hδ⟩
    let f : PathTime → R.CutDomain := fun t => ⟨δ t, hδ t⟩
    have hf : Continuous f := δ.continuous.subtype_mk _
    have he := ((R.isLocallyConstant_side hH).comp_continuous hf).apply_eq_of_preconnectedSpace
      (0 : PathTime) 1
    change (if δ 0 ∈ closure (jordanInterior H) then false else true) =
      (if δ 1 ∈ closure (jordanInterior H) then false else true) at he
    rw [h0, h1] at he
    exact he

theorem right_iff_avoidingPath (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 1) :
    z ∉ closure (jordanInterior H) ↔ DiskAvoidingPath R.crosscut.toContinuousMap z
      (halfPlaneDisk (((R.curve ⟨0, bot_lt_top⟩).re + 1 : ℝ) : ℂ)) := by
  let a := (R.curve ⟨0, bot_lt_top⟩).re + 1
  have ha : (R.curve ⟨0, bot_lt_top⟩).re < a := lt_add_one _
  have hmiss : halfPlaneDisk a ∉ range R.crosscut := by
    rw [R.boundary_hit_iff]
    exact ne_of_gt ha
  let y : R.CutDomain := ⟨halfPlaneDisk a,
    Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using (cayleyBoundary_norm a).le), hmiss⟩
  have hy : R.side H y = true := by
    exact ite_eq_right (R.boundary_right hH ha)
  constructor
  · intro hn
    have hm : z ∉ range R.crosscut := fun hp => hn (frontier_subset_closure (hH ▸ Or.inl hp))
    apply (R.side_eq_iff_avoidingPath hsep hH ⟨z, hz, hm⟩ y).mp
    exact (ite_eq_right hn).trans hy.symm
  · rintro ⟨δ, h0, h1, hδ⟩
    have hm : z ∉ range R.crosscut := h0 ▸ (hδ 0).2
    have he := (R.side_eq_iff_avoidingPath hsep hH ⟨z, hz, hm⟩ y).mpr ⟨δ, h0, h1, hδ⟩
    rw [hy] at he
    intro hi
    change (if z ∈ closure (jordanInterior H) then false else true) = true at he
    rw [ite_eq_left hi] at he
    cases he

theorem left_iff_hit_or_avoidingPath (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 1) :
    z ∈ closure (jordanInterior H) ↔ z ∈ range R.crosscut ∨
      DiskAvoidingPath R.crosscut.toContinuousMap z
        (halfPlaneDisk (((R.curve ⟨0, bot_lt_top⟩).re - 1 : ℝ) : ℂ)) := by
  let a := (R.curve ⟨0, bot_lt_top⟩).re - 1
  have ha : a < (R.curve ⟨0, bot_lt_top⟩).re := sub_one_lt _
  have hmiss : halfPlaneDisk a ∉ range R.crosscut := by
    rw [R.boundary_hit_iff]
    exact ne_of_lt ha
  let y : R.CutDomain := ⟨halfPlaneDisk a,
    Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using (cayleyBoundary_norm a).le), hmiss⟩
  have hy : R.side H y = false := by
    have hb := R.side_boundary hH a hmiss
    exact hb.trans (ite_eq_left ha.le)
  constructor
  · intro hi
    by_cases hm : z ∈ range R.crosscut
    · exact Or.inl hm
    · right
      apply (R.side_eq_iff_avoidingPath hsep hH ⟨z, hz, hm⟩ y).mp
      exact (ite_eq_left hi).trans hy.symm
  · rintro (hm | hp)
    · exact frontier_subset_closure (hH ▸ Or.inl hm)
    · obtain ⟨δ, h0, h1, hδ⟩ := hp
      have hm : z ∉ range R.crosscut := h0 ▸ (hδ 0).2
      have he := (R.side_eq_iff_avoidingPath hsep hH ⟨z, hz, hm⟩ y).mpr ⟨δ, h0, h1, hδ⟩
      rw [hy] at he
      by_contra hi
      change (if z ∈ closure (jordanInterior H) then false else true) = false at he
      rw [ite_eq_right hi] at he
      cases he

end HalfPlaneRay
end CircleDomainRigidity

end

end OAI
