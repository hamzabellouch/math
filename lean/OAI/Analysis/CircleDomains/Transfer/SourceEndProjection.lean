import OAI.Analysis.CircleDomains.Transfer.RealEndCorrespondence
import OAI.Analysis.CircleDomains.Selection.ScalarEndCaps
import OAI.Analysis.CircleDomains.Uniformization.ConformalInverse

namespace OAI

/-! An actual projection from the limiting sphere to the source quotient,
using the inverse on the domain and the matched end on its complement. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε}
namespace AssignedRealModelLimit
variable (L : AssignedRealModelLimit M)

 structure SourceEndAt (p : Sphere) where
  source : Sphere
  outside : source ∈ Gᶜ
  matching : RealTargetEnd L source
  point_eq : matching.point = p

 def chosenSourceEnd (hG : IsOpen G) (p : Sphere)
    (hp : p ∉ extendAtInfinity L.function '' G) : L.SourceEndAt p := by
  classical
  exact Classical.choice (show Nonempty (L.SourceEndAt p) from by
    obtain ⟨q, hq, E, he⟩ := L.exists_source_end hG hp
    exact ⟨⟨q, hq, E, he⟩⟩)

 def sourceProjection (hG : IsOpen G) (π : Sphere → Sphere) (p : Sphere) : Sphere := by
  classical
  exact if hp : p ∈ extendAtInfinity L.function '' G then
    π (invFunOn (extendAtInfinity L.function) G p)
    else π (L.chosenSourceEnd hG p hp).source

 theorem sourceProjection_on_image (hG : IsOpen G) (π : Sphere → Sphere)
    {x : Sphere} (hx : x ∈ G) :
    L.sourceProjection hG π (extendAtInfinity L.function x) = π x := by
  rw [sourceProjection, dite_eq_left (mem_image_of_mem _ hx),
    L.conformal.bijOn.injOn.leftInvOn_invFunOn hx]

 theorem sourceProjection_off_image (hG : IsOpen G) (π : Sphere → Sphere)
    {p : Sphere} (hp : p ∉ extendAtInfinity L.function '' G) :
    L.sourceProjection hG π p = π (L.chosenSourceEnd hG p hp).source := by
  simp only [sourceProjection, dite_eq_right hp]

end AssignedRealModelLimit

namespace RealTargetEnd
variable {L : AssignedRealModelLimit M} {q q' : Sphere}
  (E : RealTargetEnd L q)

 theorem source_in_cap_of_target_interior (E' : RealTargetEnd L q') (hq' : q' ∈ Gᶜ)
    (n : ℕ)
    (hp : E'.point ∈ ((↑) : ℂ → Sphere) '' jordanInterior (L.contours n (E.address n))) :
    q' ∈ closedTerminalCap ((L.cores n).disk (E.address n)) := by
  have hp' : E'.point ∈ closedTerminalCap (L.contours n (E'.address n)) :=
    mem_iInter.mp (E'.target ▸ mem_connectedComponentIn E'.outside) n
  have he : E'.address n = E.address n := by
    by_contra hne
    exact Set.disjoint_left.mp (disjoint_closedTerminalCaps (L.contours n) (L.disjoint n) hne)
      hp' ((image_mono subset_closure) hp)
  have hqcap := mem_iInter.mp (E'.source ▸ mem_connectedComponentIn hq') n
  rwa [he] at hqcap

 theorem projection_in_source_cap (hG : IsOpen G) (π : Sphere → Sphere) (n : ℕ)
    {p : Sphere} (hp : p ∈ ((↑) : ℂ → Sphere) '' jordanInterior (L.contours n (E.address n))) :
    ∃ x ∈ closedTerminalCap ((L.cores n).disk (E.address n)),
      L.sourceProjection hG π p = π x := by
  by_cases hpG : p ∈ extendAtInfinity L.function '' G
  · have ht : p ∈ extendAtInfinity L.function ''
        (G ∩ ((↑) : ℂ → Sphere) '' jordanInterior ((L.cores n).disk (E.address n))) := by
      rw [L.side]
      exact ⟨hpG, hp⟩
    obtain ⟨x, hx, he⟩ := ht
    refine ⟨x, ?_, ?_⟩
    · exact image_mono subset_closure hx.2
    · rw [← he, L.sourceProjection_on_image hG π hx.1]
  · let A := L.chosenSourceEnd hG p hpG
    refine ⟨A.source, E.source_in_cap_of_target_interior A.matching A.outside n ?_, ?_⟩
    · rwa [A.point_eq]
    · exact L.sourceProjection_off_image hG π hpG

end RealTargetEnd
end CircleDomainRigidity.FiniteTransfer

end

end OAI
