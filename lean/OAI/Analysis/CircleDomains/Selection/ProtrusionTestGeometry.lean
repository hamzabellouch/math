import OAI.Analysis.CircleDomains.Selection.RealEndProtrusion
import OAI.Analysis.CircleDomains.Selection.RealAnchorRetention
import OAI.Analysis.CircleDomains.Transfer.SourceAnchor
import OAI.Analysis.CircleDomains.Selection.ProtrusionProjection

namespace OAI

/-! Fixed source anchors, bounded target regions and positive transverse widths constructed
from a genuine protrusion of an assigned marked component. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

structure LocalEndTestGeometry {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere}
    {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
    (E : RealTargetEnd A q) where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  continuum : Set ℂ
  compact : IsCompact continuum
  in_component : continuum ⊆ E.plane
  in_region : continuum ⊆ closedBall center radius
  sourceAnchor : ℂ ≃ₜ ℂ
  source_inside : closure (jordanInterior sourceAnchor) ⊆ ((↑) : ℂ → Sphere) ⁻¹' G
  anchorCenter : ℂ
  anchorRadius : ℝ
  anchorRadius_pos : 0 < anchorRadius
  anchor_image : closedBall anchorCenter anchorRadius ⊆ A.function '' jordanInterior sourceAnchor
  anchor_region : closedBall anchorCenter anchorRadius ⊆ closedBall center radius
  direction : Circle
  lower : ℝ
  upper : ℝ
  width_pos : lower < upper
  projection : Icc lower upper ⊆
    (fun z => ((rotation direction).symm z).im) '' continuum ∩
      Ioo (((rotation direction).symm anchorCenter).im - anchorRadius)
        (((rotation direction).symm anchorCenter).im + anchorRadius)

namespace LocalEndTestGeometry

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  {E : RealTargetEnd A q} (T : LocalEndTestGeometry E)

def boundRadius : ℝ := max (3 * M.radius) (T.radius + ‖T.center‖)

theorem model_bound : 3 * M.radius ≤ T.boundRadius := le_max_left _ _

theorem region_bound : closedBall T.center T.radius ⊆ closedBall 0 T.boundRadius := by
  intro z hz
  rw [mem_closedBall]
  calc
    dist z 0 ≤ dist z T.center + dist T.center 0 := dist_triangle _ _ _
    _ ≤ T.radius + ‖T.center‖ := by
      rw [dist_zero_right]
      linarith [mem_closedBall.mp hz]
    _ ≤ T.boundRadius := le_max_right _ _

end LocalEndTestGeometry

namespace RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd A q)

theorem exists_local_test_geometry (hG : IsOpen G)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) {s : S} (hqs : π q = σ s)
    (hne : E.plane ≠ closedBall (A.center s) (A.radius s)) :
    ∃ T : LocalEndTestGeometry E,
      Disjoint (closedBall T.center (2 * T.radius)) (closedBall (A.center s) (A.radius s)) := by
  obtain ⟨x, ρ, Q, a, δ, hρ, _, hsep, hQc, hQconn, hQnt, hxQ, hQsub, hδ, hball⟩ :=
    E.exists_protrusion_and_anchor hG hr hq hqs hne
  have ha := hball (mem_closedBall_self hδ.le)
  have haimage : a ∈ A.function '' (((↑) : ℂ → Sphere) ⁻¹' G) := by
    obtain ⟨p, hp, he⟩ := ha.1
    cases p using OnePoint.rec with
    | infty => simp only [extendAtInfinity_infty] at he; exact (OnePoint.coe_ne_infty a he.symm).elim
    | coe z => exact ⟨z, hp, OnePoint.coe_injective he⟩
  obtain ⟨H, η, hη, hHG, hηsub⟩ := exists_source_jordan_anchor
    (hG.preimage OnePoint.continuous_coe) (A.plane_open_embedding hG).2.1
    isOpen_ball haimage ha.2
  obtain ⟨rot, lo, hi, hlt, hproj⟩ := exists_transverse_interval hQconn hQnt hxQ a hη
  refine ⟨{
    center := x
    radius := ρ
    radius_pos := hρ
    continuum := Q
    compact := hQc
    in_component := fun z hz => (hQsub hz).1
    in_region := fun z hz => ball_subset_closedBall (hQsub hz).2
    sourceAnchor := H
    source_inside := hHG
    anchorCenter := a
    anchorRadius := η
    anchorRadius_pos := hη
    anchor_image := fun z hz => (hηsub hz).1
    anchor_region := fun z hz => ball_subset_closedBall (hηsub hz).2
    direction := rot⁻¹
    lower := lo
    upper := hi
    width_pos := hlt
    projection := by simpa only [rotation_symm, inv_inv] using hproj
  }, hsep⟩

end RealTargetEnd
end CircleDomainRigidity.FiniteTransfer

end

end OAI
