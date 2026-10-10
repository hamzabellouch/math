import OAI.Analysis.CircleDomains.Topology.ConnectedExteriorNeighborhood

namespace OAI

/-! A nonempty compact nonseparating plane continuum has arbitrarily
small Jordan-disk neighborhoods. The finite contour cover reduces to one
disk by connectedness; no sphere-decomposition theorem is used. -/
open Set Topology
noncomputable section
namespace CircleDomainRigidity

lemma connected_subset_one_of_disjoint_open_cover
    {X ι : Type*} [TopologicalSpace X] {K : Set X} (hK : IsConnected K)
    (s : Set ι) (D : ι → Set X) (hD : ∀ i ∈ s, IsOpen (D i))
    (hd : s.Pairwise (fun i j => Disjoint (D i) (D j)))
    (hcover : K ⊆ ⋃ i ∈ s, D i) : ∃ i ∈ s, K ⊆ D i := by
  classical
  obtain ⟨x,hx⟩ := hK.nonempty
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hcover hx)
  let V := ⋃ j ∈ s \ {i}, D j
  have hV : IsOpen V := isOpen_biUnion fun j hj => hD j hj.1
  have hdisj : Disjoint (D i) V := by
    apply Set.disjoint_left.mpr
    intro y hyI hyV
    obtain ⟨j,hj,hyj⟩ := mem_iUnion₂.mp hyV
    exact Set.disjoint_left.mp (hd hi hj.1 (fun he => hj.2 (mem_singleton_iff.mpr he.symm))) hyI hyj
  have hc : K ⊆ D i ∪ V := by
    intro y hy
    obtain ⟨j,hj,hyj⟩ := mem_iUnion₂.mp (hcover hy)
    by_cases he : j=i
    · exact Or.inl (he ▸ hyj)
    · exact Or.inr (mem_iUnion₂.mpr ⟨j,⟨hj,by simpa using he⟩,hyj⟩)
  exact ⟨i,hi,hK.isPreconnected.subset_left_of_subset_union
    (hD i hi) hV hdisj hc ⟨x,hx,hxi⟩⟩

lemma exists_jordan_neighborhood_of_nonseparating_continuum
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {K U : Set ℂ} (hK : IsCompact K) (hc : IsConnected K)
    (hcomp : IsConnected Kᶜ) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ H : ℂ ≃ₜ ℂ, K ⊆ jordanInterior H ∧ closure (jordanInterior H) ⊆ U := by
  obtain ⟨V,hV,hKV,hVU,hVc,hVunbounded⟩ :=
    exists_open_connected_exterior_neighborhood hK hcomp hU hKU
  obtain ⟨f,t,γ,H,s,_,hcover,hd,hinside,_⟩ :=
    exists_finite_smooth_jordan_cover hsard hsch hK (Subset.rfl)
      (by simp) hV hKV hVc.isPreconnected hVunbounded
  obtain ⟨i,hi,hKi⟩ := connected_subset_one_of_disjoint_open_cover hc s
    (fun i => jordanInterior (H i)) (fun i _ => jordanInterior_isOpen (H i))
    (fun i hi j hj hij => (hd hi hj hij).mono subset_closure subset_closure) hcover
  exact ⟨H i,hKi,(hinside i hi).trans hVU⟩

end CircleDomainRigidity

end

end OAI
