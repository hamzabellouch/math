import OAI.Analysis.CircleDomains.Selection.ProtrusionGeometry

namespace OAI

/-! Protrusion localization for the actual marked components of the real-model limit. -/

open Set Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd L q)

/-- Removing infinity preserves these complementary components, which all
lie in the finite plane. -/
theorem plane_eq_component {x : ℂ} (hx : x ∈ E.plane) :
    E.plane = connectedComponentIn
      (((↑) : ℂ → Sphere) ⁻¹' (extendAtInfinity L.function '' G)ᶜ) x := by
  let D : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' (extendAtInfinity L.function '' G)ᶜ
  have hED : E.plane ⊆ D := fun _ hz =>
    connectedComponentIn_subset (extendAtInfinity L.function '' G)ᶜ E.point hz
  apply Subset.antisymm
  · exact E.plane_connected.isPreconnected.subset_connectedComponentIn hx hED
  · have himage : IsPreconnected (((↑) : ℂ → Sphere) '' connectedComponentIn D x) :=
      isPreconnected_connectedComponentIn.image _ OnePoint.continuous_coe.continuousOn
    have hsub : ((↑) : ℂ → Sphere) '' connectedComponentIn D x ⊆
        connectedComponentIn (extendAtInfinity L.function '' G)ᶜ (x : Sphere) :=
      himage.subset_connectedComponentIn
        (mem_image_of_mem _ (mem_connectedComponentIn (hED hx)))
        (by
          rintro _ ⟨z, hz, rfl⟩
          exact connectedComponentIn_subset D x hz)
    rw [← connectedComponentIn_eq hx] at hsub
    exact fun z hz => hsub (mem_image_of_mem _ hz)

/-- If an assigned marked disk does not fill its component, there is a
nontrivial local continuum outside the disk and a nearby genuine target
ball serving as the anchor for the barrier/stream alternatives. -/
theorem exists_protrusion_and_anchor
    (hG : IsOpen G)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) {s : S} (hqs : π q = σ s)
    (hne : E.plane ≠ closedBall (L.center s) (L.radius s)) :
    ∃ (x : ℂ) (ρ : ℝ) (Q : Set ℂ) (a : ℂ) (δ : ℝ),
      0 < ρ ∧ x ∈ frontier E.plane ∧
      Disjoint (closedBall x (2 * ρ)) (closedBall (L.center s) (L.radius s)) ∧
      IsCompact Q ∧ IsConnected Q ∧ Q.Nontrivial ∧ x ∈ Q ∧
      Q ⊆ E.plane ∩ ball x ρ ∧ 0 < δ ∧
      closedBall a δ ⊆ (((↑) : ℂ → Sphere) ⁻¹' (extendAtInfinity L.function '' G)) ∩ ball x ρ := by
  have hD : closedBall (L.center s) (L.radius s) ⊆ E.plane := by
    intro z hz
    exact E.marked_disk_subset hr hq hqs (mem_image_of_mem _ hz)
  obtain ⟨x, ρ, Q, hρ, hx, hd, hQc, hQconn, hQnt, hxQ, hQsub⟩ :=
    exists_local_protrusion E.plane_compact E.plane_connected (L.bounds s).2.1 hD hne
  have hxE : x ∈ E.plane := E.plane_compact.isClosed.closure_eq ▸ hx.1
  have hU : IsOpen (((↑) : ℂ → Sphere) ⁻¹' (extendAtInfinity L.function '' G)) :=
    (L.conformal.1.isOpen_image hG hG (Subset.refl G)).preimage OnePoint.continuous_coe
  have hxfront : x ∈ frontier (connectedComponentIn
      ((((↑) : ℂ → Sphere) ⁻¹' (extendAtInfinity L.function '' G))ᶜ) x) := by
    simpa only [← preimage_compl, ← E.plane_eq_component hxE] using hx
  obtain ⟨a, δ, hδ, hanchor⟩ := exists_domain_ball_near_component_frontier hU
    (connectedComponentIn_subset (extendAtInfinity L.function '' G)ᶜ E.point hxE) hxfront hρ
  exact ⟨x, ρ, Q, a, δ, hρ, hx, hd, hQc, hQconn, hQnt, hxQ, hQsub, hδ, hanchor⟩

end CircleDomainRigidity.FiniteTransfer.RealTargetEnd

end

end OAI
