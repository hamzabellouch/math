import OAI.Analysis.CircleDomains.Transfer.ContinuousSourceProjection

namespace OAI

/-! The constructed projection takes the prescribed source value on the
whole corresponding complementary component and covers the source quotient. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M}

 theorem RealTargetEnd.sourceProjection_eq {q : Sphere} (E : RealTargetEnd L q)
    (hG : IsOpen G) (π : Sphere → Sphere)
    (hc : ∀ q p, p ∈ connectedComponentIn Gᶜ q → π p = π q)
    {p : Sphere} (hp : p ∈ connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point) :
    L.sourceProjection hG π p = π q := by
  have hout : p ∉ extendAtInfinity L.function '' G := connectedComponentIn_subset _ _ hp
  let A := L.chosenSourceEnd hG p hout
  have hsource : A.source ∈ connectedComponentIn Gᶜ q := by
    rw [E.source]
    apply mem_iInter.mpr
    intro n
    apply E.source_in_cap_of_target_interior A.matching A.outside n
    have ht := E.nested n (mem_iInter.mp (E.target ▸ hp) (n + 1))
    exact (congrArg (fun t : Sphere => t ∈ ((↑) : ℂ → Sphere) ''
      jordanInterior (L.contours n (E.address n))) A.point_eq).mpr ht
  exact (L.sourceProjection_off_image hG π hout).trans (hc q A.source hsource)

 theorem AssignedRealModelLimit.sourceProjection_surjective (L : AssignedRealModelLimit M)
    (hG : IsOpen G) (π : Sphere → Sphere) (hs : Surjective π)
    (hc : ∀ q p, p ∈ connectedComponentIn Gᶜ q → π p = π q) :
    Surjective (L.sourceProjection hG π) := by
  intro y
  obtain ⟨q, rfl⟩ := hs y
  by_cases hq : q ∈ G
  · exact ⟨extendAtInfinity L.function q, L.sourceProjection_on_image hG π hq⟩
  · obtain ⟨E⟩ := L.exists_target_end hG hq
    exact ⟨E.point, E.sourceProjection_eq hG π hc (mem_connectedComponentIn E.outside)⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
