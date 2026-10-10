import OAI.Analysis.CircleDomains.Selection.ProjectionEndFibers
import OAI.Analysis.CircleDomains.Transfer.ContinuousSourceProjection

namespace OAI

/-! Matched Jordan ends for a fixed conformal equivalence, independently
of the finite-model representation used to construct that equivalence. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

structure MatchedConformalEnds (G : Set Sphere) (f : Sphere → Sphere) where
  cores : ℕ → SmoothJordanCore G
  disks : (n : ℕ) → Fin (cores n).count → ℂ ≃ₜ ℂ
  strict : ∀ n, (cores n).carrier ⊆ interior (cores (n+1)).carrier
  cover : (⋃ n, interior (cores n).carrier) = G
  disjoint : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (disks n i)))
  complement : ∀ n, (f '' (cores n).carrier)ᶜ =
    ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (disks n i)
  boundary : ∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((cores n).disk i))) =
    ((↑) : ℂ → Sphere) '' frontier (jordanInterior (disks n i))
  side : ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((cores n).disk i))) =
    f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (disks n i))

 theorem exists_matched_conformal_ends
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) {G : Set Sphere} (hG : IsOpen G) (hc : IsConnected G)
    (hinf : OnePoint.infty ∈ G) {f : Sphere → Sphere}
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty) :
    Nonempty (MatchedConformalEnds G f) := by
  obtain ⟨C,J,hs,hc,hd,he,hb,hi⟩ := exists_matched_jordan_exhaustion
    hsard hsch hG hc hinf hf.1 hf.bijOn.injOn hfix
  exact ⟨⟨C,J,hs,hc,hd,he,hb,hi⟩⟩

namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem front_source (n : ℕ) (i : Fin (D.cores n).count) :
    ((↑) : ℂ → Sphere) '' frontier (jordanInterior ((D.cores n).disk i)) ⊆ G :=
  (D.cores n).boundary_subset_domain i

 structure EndAt (p : Sphere) where
  source : Sphere
  outside : source ∈ Gᶜ
  address : (n : ℕ) → Fin (D.cores n).count
  source_eq : connectedComponentIn Gᶜ source =
    ⋂ n, closedTerminalCap ((D.cores n).disk (address n))
  target_eq : connectedComponentIn (f '' G)ᶜ p =
    ⋂ n, closedTerminalCap (D.disks n (address n))
  source_nested : ∀ n, closedTerminalCap ((D.cores (n+1)).disk (address (n+1))) ⊆
    ((↑) : ℂ → Sphere) '' jordanInterior ((D.cores n).disk (address n))

 def endAt (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    (p : Sphere) (hp : p ∈ (f '' G)ᶜ) : D.EndAt p :=
  Classical.choice (show Nonempty (D.EndAt p) from by
    obtain ⟨b,q,hq,hs,ht,hn⟩ := corresponding_source_end_of_target hG hf.1 hf.bijOn.injOn
      D.cores D.disks D.strict D.cover D.disjoint D.complement D.boundary D.side hp
    exact ⟨⟨q,hq,b,hs,ht,hn⟩⟩)

 def projection (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    (p : Sphere) : Sphere := by
  classical
  exact if hp : p ∈ f '' G then invFunOn f G p else (D.endAt hG hf p hp).source

 theorem projection_on_image (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    {x : Sphere} (hx : x ∈ G) : D.projection hG hf (f x) = x := by
  rw [projection,dite_eq_left (mem_image_of_mem f hx),hf.bijOn.injOn.leftInvOn_invFunOn hx]

 theorem projection_outside (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    {p : Sphere} (hp : p ∉ f '' G) : D.projection hG hf p ∈ Gᶜ := by
  rw [projection,dite_eq_right hp]
  exact (D.endAt hG hf p hp).outside

namespace EndAt
variable {D} {p : Sphere} (E : D.EndAt p)

 theorem target_nested (hf : IsConformalEquivalence f G (f '' G)) (n : ℕ) :
    closedTerminalCap (D.disks (n+1) (E.address (n+1))) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior (D.disks n (E.address n)) :=
  (matched_jordan_disk_subset_iff hf.bijOn.injOn _ _ _ _
    (D.front_source _ _) (D.boundary _ _) (D.side _ _)).mp (E.source_nested n)

 theorem source_in_cap {p' : Sphere} (E' : D.EndAt p')
    (hp' : p' ∈ (f '' G)ᶜ) (n : ℕ)
    (hinside : p' ∈ ((↑) : ℂ → Sphere) '' jordanInterior (D.disks n (E.address n))) :
    E'.source ∈ closedTerminalCap ((D.cores n).disk (E.address n)) := by
  have hpCap := mem_iInter.mp (E'.target_eq ▸ mem_connectedComponentIn hp') n
  have he : E'.address n = E.address n := by
    by_contra hne
    exact Set.disjoint_left.mp (disjoint_closedTerminalCaps (D.disks n) (D.disjoint n) hne)
      hpCap ((image_mono subset_closure) hinside)
  have hqCap := mem_iInter.mp (E'.source_eq ▸ mem_connectedComponentIn E'.outside) n
  rwa [he] at hqCap

 theorem projection_in_cap (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    (n : ℕ) {y : Sphere}
    (hy : y ∈ ((↑) : ℂ → Sphere) '' jordanInterior (D.disks n (E.address n))) :
    D.projection hG hf y ∈ closedTerminalCap ((D.cores n).disk (E.address n)) := by
  by_cases hyG : y ∈ f '' G
  · have hh : y ∈ f '' (G ∩ (((↑) : ℂ → Sphere) ''
        jordanInterior ((D.cores n).disk (E.address n)))) := by
      rw [D.side]
      exact ⟨hyG,hy⟩
    obtain ⟨x,hx,rfl⟩ := hh
    rw [D.projection_on_image hG hf hx.1]
    exact (image_mono subset_closure) hx.2
  · rw [projection,dite_eq_right hyG]
    exact E.source_in_cap (D.endAt hG hf y hyG) hyG n hy

end EndAt

 theorem projection_continuous (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (hTD : IsTotallyDisconnected Gᶜ) :
    Continuous (D.projection hG hf) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ f '' G
  · obtain ⟨x,hx,rfl⟩ := hp
    have hi := continuousAt_conformal_invFunOn hf.1 hG hf.bijOn.injOn hx
    have hval : D.projection hG hf (f x) = invFunOn f G (f x) := by
      rw [projection,dite_eq_left (mem_image_of_mem f hx)]
    change Tendsto (D.projection hG hf) (𝓝 (f x)) (𝓝 (D.projection hG hf (f x)))
    rw [hval]
    apply hi.tendsto.congr'
    filter_upwards [(hf.1.isOpen_image hG hG Subset.rfl).mem_nhds (mem_image_of_mem f hx)] with y hy
    simp only [projection,dite_eq_left hy]
  · let E := D.endAt hG hf p hp
    have hval : D.projection hG hf p = E.source := by rw [projection,dite_eq_right hp]
    change Tendsto (D.projection hG hf) (𝓝 p) (𝓝 (D.projection hG hf p))
    rw [hval]
    apply tendsto_nhds.mpr
    intro V hV hpV
    have hsingle : connectedComponentIn Gᶜ E.source = {E.source} :=
      (hTD _ (connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn).eq_singleton_of_mem
        (mem_connectedComponentIn E.outside)
    obtain ⟨n,hn⟩ := nested_sphere_sets_eventually_subset
      (fun n => (isCompact_closedTerminalCap ((D.cores n).disk (E.address n))).isClosed)
      (antitone_nat_of_succ_le (fun n => (E.source_nested n).trans (image_mono subset_closure)))
      hV (by rw [← E.source_eq,hsingle]; exact singleton_subset_iff.mpr hpV)
    have hpInside : p ∈ ((↑) : ℂ → Sphere) '' jordanInterior (D.disks n (E.address n)) :=
      E.target_nested hf n (mem_iInter.mp (E.target_eq ▸ mem_connectedComponentIn hp) (n+1))
    filter_upwards [(OnePoint.isOpen_image_coe.mpr
      (jordanInterior_isOpen (D.disks n (E.address n)))).mem_nhds hpInside] with y hy
    exact hn (E.projection_in_cap hG hf n hy)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
