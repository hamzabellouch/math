import OAI.Analysis.CircleDomains.Rigidity.MatchedConformalEnds

namespace OAI

/-! Singleton complementary components make the continuous inverse end
projection bijective, giving the actual sphere homeomorphism extension. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem projection_surjective (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (hTD : IsTotallyDisconnected Gᶜ) :
    Surjective (D.projection hG hf) := by
  have hP := D.projection_continuous hG hf hTD
  intro q
  by_cases hq : q ∈ G
  · exact ⟨f q,D.projection_on_image hG hf hq⟩
  · obtain ⟨b,p,hp,hsource,htarget,_⟩ := corresponding_target_end_of_source hG hf.1
      hf.bijOn.injOn D.cores D.disks D.strict D.cover D.disjoint D.complement D.boundary D.side hq
    have hcaps (n : ℕ) : D.projection hG hf p ∈ closedTerminalCap ((D.cores n).disk (b n)) := by
      apply inverse_projection_matched_cap hG hP
        (fun x hx => D.projection_on_image hG hf hx)
        (fun y hy => D.projection_outside hG hf hy)
        ((D.cores n).disk (b n)) (D.disks n (b n)) (D.front_source n (b n))
        (D.boundary n (b n)) (D.side n (b n))
      exact mem_image_of_mem _ (mem_iInter.mp (htarget ▸ mem_connectedComponentIn hp) n)
    have hmem : D.projection hG hf p ∈ connectedComponentIn Gᶜ q := by
      rw [hsource]
      exact mem_iInter.mpr hcaps
    have hsingle := (hTD _ (connectedComponentIn_subset Gᶜ q)
      isPreconnected_connectedComponentIn).eq_singleton_of_mem (mem_connectedComponentIn hq)
    exact ⟨p,by simpa only [hsingle,mem_singleton_iff] using hmem⟩

 theorem projection_injective (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hTD : IsTotallyDisconnected Gᶜ) (hT : IsTotallyDisconnected (f '' G)ᶜ) :
    Injective (D.projection hG hf) := by
  have hP := D.projection_continuous hG hf hTD
  intro x y hxy
  by_cases hx : x ∈ f '' G
  · obtain ⟨z,hz,rfl⟩ := hx
    have hyz : D.projection hG hf y = z := hxy.symm.trans (D.projection_on_image hG hf hz)
    exact ((inverse_projection_fiber_on_domain
      (fun z hz => D.projection_on_image hG hf hz)
      (fun p hp => D.projection_outside hG hf hp) hz).mp hyz).symm
  · have hfiber := inverse_projection_component_eq_fiber hG hTD hf.1 hf.bijOn.injOn hP
      (fun z hz => D.projection_on_image hG hf hz)
      (fun p hp => D.projection_outside hG hf hp)
      D.cores D.disks D.strict D.cover D.disjoint D.complement D.boundary D.side hx
    have hy : y ∈ connectedComponentIn (f '' G)ᶜ x := by
      rw [hfiber]
      exact hxy.symm
    exact hT _ (connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn
      (mem_connectedComponentIn hx) hy

 include D in
 theorem exists_homeomorph_extension (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hTD : IsTotallyDisconnected Gᶜ) (hT : IsTotallyDisconnected (f '' G)ᶜ) :
    ∃ H : Sphere ≃ₜ Sphere, ∀ x ∈ G, H x = f x := by
  let e : Sphere ≃ Sphere := Equiv.ofBijective (D.projection hG hf)
    ⟨D.projection_injective hG hf hTD hT,D.projection_surjective hG hf hTD⟩
  have hc : Continuous e := D.projection_continuous hG hf hTD
  let H := e.toHomeomorphOfContinuousClosed hc hc.isClosedMap
  refine ⟨H.symm,?_⟩
  intro x hx
  apply H.injective
  rw [H.apply_symm_apply]
  change x = D.projection hG hf (f x)
  exact (D.projection_on_image hG hf hx).symm

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
