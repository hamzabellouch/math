import OAI.Analysis.CircleDomains.Selection.RaySideConnectivity
import Mathlib.Topology.Connected.LocallyPathConnected

namespace OAI

/-! A closed-disk crosscut complement is locally path connected. Thus the
connected sides already proved are its actual path components. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.HalfPlaneRay

 theorem cutDomain_locallyPathConnected (R : HalfPlaneRay) : LocallyPathConnectedSpace R.CutDomain := by
  constructor
  intro x
  rw [Filter.hasBasis_self]
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨r, hr, hrmiss⟩ := Metric.isOpen_iff.mp
    (isCompact_range R.crosscut.continuous).isClosed.isOpen_compl x.val x.property.2
  let d := min ε r
  have hd : 0 < d := lt_min hε hr
  refine ⟨Metric.ball x d, Metric.ball_mem_nhds _ hd, ?_, ?_⟩
  · apply Topology.IsInducing.subtypeVal.isPathConnected_iff.mpr
    have he : Subtype.val '' Metric.ball x d =
        Metric.ball x.val d ∩ Metric.closedBall (0 : ℂ) 1 := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨hw, w.property.1⟩
      · intro hz
        have hzr : z ∈ Metric.ball x.val r :=
          (Metric.ball_subset_ball (min_le_right ε r)) hz.1
        have hm : z ∉ range R.crosscut := hrmiss hzr
        exact ⟨⟨z, hz.2, hm⟩, hz.1, rfl⟩
    rw [he]
    exact ((convex_ball x.val d).inter (convex_closedBall (0 : ℂ) 1)).isPathConnected
      ⟨x.val, Metric.mem_ball_self hd, x.property.1⟩
  · exact (Metric.ball_subset_ball (min_le_left _ _)).trans hεU

 theorem side_fiber_preconnected (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) (b : Bool) :
    IsPreconnected {z : R.CutDomain | R.side H z = b} := by
  apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
  cases b with
  | false =>
    have he : Subtype.val '' {z : R.CutDomain | R.side H z = false} =
        closure (jordanInterior H) \ range R.crosscut := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨?_, w.property.2⟩
        by_contra hn
        change (if w.val ∈ closure (jordanInterior H) then false else true) = false at hw
        rw [ite_eq_right hn] at hw
        cases hw
      · intro hz
        refine ⟨⟨z, (R.filling_subset hH).1 hz.1, hz.2⟩, ?_, rfl⟩
        exact ite_eq_left hz.1
    rw [he]
    exact (R.leftSide_connected H hH).isPreconnected
  | true =>
    have he : Subtype.val '' {z : R.CutDomain | R.side H z = true} =
        Metric.closedBall 0 1 \ closure (jordanInterior H) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨w.property.1, ?_⟩
        intro hi
        change (if w.val ∈ closure (jordanInterior H) then false else true) = true at hw
        rw [ite_eq_left hi] at hw
        cases hw
      · intro hz
        have hm : z ∉ range R.crosscut := fun hp => hz.2
          (frontier_subset_closure (hH ▸ Or.inl hp))
        refine ⟨⟨z, hz.1, hm⟩, ?_, rfl⟩
        exact ite_eq_right hz.2
    rw [he]
    exact (R.rightSide_connected hsep H hH).isPreconnected

 theorem side_eq_iff_joined (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) (x y : R.CutDomain) :
    R.side H x = R.side H y ↔ Joined x y := by
  let : LocallyPathConnectedSpace R.CutDomain := R.cutDomain_locallyPathConnected
  constructor
  · intro he
    have hc : IsConnected {z : R.CutDomain | R.side H z = R.side H x} :=
      ⟨⟨x, rfl⟩, R.side_fiber_preconnected hsep hH _⟩
    have hp := ((R.isLocallyConstant_side hH).isOpen_fiber _).isConnected_iff_isPathConnected.mp hc
    exact (hp.joinedIn x rfl y he.symm).joined
  · intro h
    have hc := h.somePath.continuous
    have he := ((R.isLocallyConstant_side hH).comp_continuous hc).apply_eq_of_preconnectedSpace
      (0 : PathTime) 1
    simpa only [Function.comp_apply, Path.source, Path.target] using he

end CircleDomainRigidity.HalfPlaneRay

end

end OAI
