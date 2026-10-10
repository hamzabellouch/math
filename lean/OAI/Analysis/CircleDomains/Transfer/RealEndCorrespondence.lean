import OAI.Analysis.CircleDomains.Transfer.RealTargetEnds

namespace OAI

/-! Every target end has a source address, and that address identifies its marked disk. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} (L : AssignedRealModelLimit M)

theorem AssignedRealModelLimit.exists_source_end
    (hG : IsOpen G) {p : Sphere} (hp : p ∈ (extendAtInfinity L.function '' G)ᶜ) :
    ∃ q ∈ Gᶜ, ∃ E : RealTargetEnd L q, E.point = p := by
  obtain ⟨b, q, hq, hs, ht, hn⟩ := corresponding_source_end_of_target hG
    L.conformal.1 L.conformal.bijOn.injOn L.cores L.contours L.nested L.exhausts
    L.disjoint L.image_core L.boundary L.side hp
  have htn (n : ℕ) : closedTerminalCap (L.contours (n + 1) (b (n + 1))) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior (L.contours n (b n)) :=
    (matched_jordan_disk_subset_iff L.conformal.bijOn.injOn
      ((L.cores n).disk (b n)) ((L.cores (n + 1)).disk (b (n + 1)))
      (L.contours n (b n)) (L.contours (n + 1) (b (n + 1)))
      ((L.cores (n + 1)).boundary_subset_domain (b (n + 1)))
      (L.boundary (n + 1) (b (n + 1))) (L.side n (b n))).mp (hn n)
  exact ⟨q, hq, ⟨b, p, hp, hs, ht, htn⟩, rfl⟩

namespace RealTargetEnd

variable {L} {q : Sphere} (E : RealTargetEnd L q)

theorem marked_disk_subset
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) {s : S} (hqs : π q = σ s) :
    ((↑) : ℂ → Sphere) '' Metric.closedBall (L.center s) (L.radius s) ⊆
      connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point := by
  obtain ⟨b, p, _, hs, ht, hdisk, _⟩ := L.marked s
  have hqm : q ∈ connectedComponentIn Gᶜ (d.sourceMark s) := by
    rw [d.sourceMark_component hr s]
    exact hqs
  have hqE : q ∈ ⋂ n, closedTerminalCap ((L.cores n).disk (E.address n)) :=
    E.source ▸ mem_connectedComponentIn hq
  have hqb : q ∈ ⋂ n, closedTerminalCap ((L.cores n).disk (b n)) := hs ▸ hqm
  have hb (n : ℕ) : b n = E.address n := by
    by_contra hne
    exact Set.disjoint_left.mp (disjoint_closedTerminalCaps (L.cores n).disk
      (L.cores n).disjoint hne) (mem_iInter.mp hqb n) (mem_iInter.mp hqE n)
  have hbe : b = E.address := funext hb
  rw [hbe] at ht
  exact ht.trans E.target.symm ▸ hdisk

end RealTargetEnd

end CircleDomainRigidity.FiniteTransfer

end

end OAI
