import OAI.Analysis.CircleDomains.Selection.ProtrusionTestGeometry
import OAI.Analysis.CircleDomains.Topology.GatedQuotientMap

namespace OAI

/-! The actual protrusion balls give the two target gates and a uniform
positive distance from the marked disk. The normalized source map stays
outside that disk throughout its physical domain. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

namespace LocalEndTestGeometry
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  {E : RealTargetEnd A q} (T : LocalEndTestGeometry E)

 def closedGate : Set Sphere := ((↑) : ℂ → Sphere) '' closedBall T.center T.radius
 def openGate : Set Sphere := ((↑) : ℂ → Sphere) '' ball T.center (2 * T.radius)

 theorem closed_closedGate : IsClosed T.closedGate :=
  OnePoint.isClosed_image_coe.mpr ⟨isClosed_closedBall, isCompact_closedBall _ _⟩

 theorem open_openGate : IsOpen T.openGate := OnePoint.isOpen_image_coe.mpr isOpen_ball

 theorem closedGate_subset_openGate : T.closedGate ⊆ T.openGate :=
  image_mono (closedBall_subset_ball (by linarith [T.radius_pos]))

 theorem closure_openGate : closure T.openGate =
    ((↑) : ℂ → Sphere) '' closedBall T.center (2 * T.radius) := by
  apply Subset.antisymm
  · exact closure_minimal (image_mono ball_subset_closedBall)
      (OnePoint.isClosed_image_coe.mpr ⟨isClosed_closedBall, isCompact_closedBall _ _⟩)
  · rw [← closure_ball T.center (show 2 * T.radius ≠ 0 by linarith [T.radius_pos])]
    exact image_closure_subset_closure_image OnePoint.continuous_coe

 theorem infinity_notMem_closure_openGate : OnePoint.infty ∉ closure T.openGate := by
  rw [T.closure_openGate]
  exact OnePoint.infty_notMem_image_coe

 theorem uniform_gate_gap {s : S}
    (hsep : Disjoint (closedBall T.center (2 * T.radius))
      (closedBall (A.center s) (A.radius s))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, (z : Sphere) ∈ closure T.openGate →
      δ ≤ infDist z (closedBall (A.center s) (A.radius s)) := by
  obtain ⟨δ, hδ, hgap⟩ := exists_uniform_infDist_gap
    (isCompact_closedBall T.center (2 * T.radius))
    (nonempty_closedBall.mpr (by linarith [T.radius_pos])) isClosed_closedBall
    (nonempty_closedBall.mpr (A.bounds s).2.1) hsep
  refine ⟨δ, hδ, fun z hz => hgap z ?_⟩
  rw [T.closure_openGate] at hz
  exact OnePoint.coe_injective.mem_set_image.mp hz

end LocalEndTestGeometry

namespace RealTargetEnd
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd A q)

include E in
 theorem source_outside_marked_disk
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) {s : S} (hqs : π q = σ s) :
    ∀ z : ℂ, (z : Sphere) ∈ G → A.radius s < dist (A.function z) (A.center s) := by
  intro z hz
  apply lt_of_not_ge
  intro hdist
  have hmem : (A.function z : Sphere) ∈
      connectedComponentIn (extendAtInfinity A.function '' G)ᶜ E.point :=
    E.marked_disk_subset hr hq hqs (mem_image_of_mem _ hdist)
  exact connectedComponentIn_subset _ _ hmem ⟨(z : Sphere), hz, rfl⟩

end RealTargetEnd
end CircleDomainRigidity.FiniteTransfer

end

end OAI
