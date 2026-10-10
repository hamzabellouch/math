import OAI.Analysis.CircleDomains.Topology.DiskBoundarySide

namespace OAI

/-! The two sides remain separated at the boundary of the closed disk.
Membership in the filled side is locally constant away from the crosscut. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

abbrev DiskCutDomain (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) :=
  {z : ℂ // z ∈ Metric.closedBall 0 1 \ range (diskRayCrosscut γ hγ)}

def diskCutSide (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (H : ℂ ≃ₜ ℂ) (z : DiskCutDomain γ hγ) : Bool :=
  if z.val ∈ closure (jordanInterior H) then false else true

theorem isLocallyConstant_diskCutSide (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (H : ℂ ≃ₜ ℂ)
    (hf : frontier (jordanInterior H) = range (diskRayCrosscut γ hγ) ∪
      range (boundaryClosingArc _ (compactifiedDiskRay_start_norm hγ))) :
    IsLocallyConstant (diskCutSide γ hγ H) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro z
  by_cases hz : z.val ∈ closure (jordanInterior H)
  · have hn : ∃ ε > 0, Metric.ball z.val ε ∩ Metric.closedBall 0 1 ⊆
        closure (jordanInterior H) := by
      by_cases hi : z.val ∈ jordanInterior H
      · obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.mp (jordanInterior_isOpen H) z.val hi
        exact ⟨ε, hε, fun _ h => subset_closure (hB h.1)⟩
      · have hfront : z.val ∈ frontier (jordanInterior H) := by
          rw [(jordanInterior_isOpen H).frontier_eq]
          exact ⟨hz, hi⟩
        exact diskRay_left_boundary_neighborhood γ hγ H hf hfront z.property.2
    obtain ⟨ε, hε, hB⟩ := hn
    have hnear : ∀ᶠ w : DiskCutDomain γ hγ in 𝓝 z, w.val ∈ Metric.ball z.val ε :=
      continuous_subtype_val.continuousAt.eventually
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
    filter_upwards [hnear] with w hw
    simp only [diskCutSide, ite_eq_left hz, ite_eq_left (hB ⟨hw, w.property.1⟩)]
  · have hnear : ∀ᶠ w : DiskCutDomain γ hγ in 𝓝 z,
        w.val ∈ (closure (jordanInterior H))ᶜ :=
      continuous_subtype_val.continuousAt.eventually (isClosed_closure.isOpen_compl.mem_nhds hz)
    filter_upwards [hnear] with w hw
    simp only [diskCutSide, ite_eq_right hz, ite_eq_right hw]

theorem diskCutSide_eq_on_connected (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (H : ℂ ≃ₜ ℂ)
    (hf : frontier (jordanInterior H) = range (diskRayCrosscut γ hγ) ∪
      range (boundaryClosingArc _ (compactifiedDiskRay_start_norm hγ)))
    {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    (f : T → DiskCutDomain γ hγ) (hc : Continuous f) (x y : T) :
    diskCutSide γ hγ H (f x) = diskCutSide γ hγ H (f y) :=
  ((isLocallyConstant_diskCutSide γ hγ H hf).comp_continuous hc).apply_eq_of_preconnectedSpace x y

theorem diskCutSide_path_intersection (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (H : ℂ ≃ₜ ℂ)
    (hf : frontier (jordanInterior H) = range (diskRayCrosscut γ hγ) ∪
      range (boundaryClosingArc _ (compactifiedDiskRay_start_norm hγ)))
    (δ : C(PathTime, ℂ)) (hδ : ∀ t, δ t ∈ Metric.closedBall 0 1)
    (h0 : δ 0 ∉ range (diskRayCrosscut γ hγ))
    (h1 : δ 1 ∉ range (diskRayCrosscut γ hγ))
    (hne : diskCutSide γ hγ H ⟨δ 0, hδ 0, h0⟩ ≠
      diskCutSide γ hγ H ⟨δ 1, hδ 1, h1⟩) :
    ∃ t, δ t ∈ range (diskRayCrosscut γ hγ) := by
  by_contra hn
  have hmiss : ∀ t, δ t ∉ range (diskRayCrosscut γ hγ) := by simpa only [not_exists] using hn
  let f : PathTime → DiskCutDomain γ hγ := fun t => ⟨δ t, hδ t, hmiss t⟩
  have hc : Continuous f := δ.continuous.subtype_mk _
  exact hne (diskCutSide_eq_on_connected γ hγ H hf f hc 0 1)

end CircleDomainRigidity

end

end OAI
