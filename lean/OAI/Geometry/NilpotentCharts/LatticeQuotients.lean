import Mathlib

namespace OAI

/-! Discrete projected lattices and compact quotient fibers. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawLatticeProjection
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma commutator_mul_central (a u c : G) (hc : c ∈ Subgroup.center G) :
    ⁅a,u*c⁆ = ⁅a,u⁆ := by
  have hca : c*a⁻¹ = a⁻¹*c := (Subgroup.mem_center_iff.mp hc a⁻¹).symm
  simp only [commutatorElement_def,mul_inv_rev]
  calc
    _ = a*u*(c*a⁻¹)*c⁻¹*u⁻¹ := by group
    _ = a*u*(a⁻¹*c)*c⁻¹*u⁻¹ := by rw [hca]
    _ = _ := by group

 

theorem discrete_map (Γ S : Subgroup G) [DiscreteTopology Γ] [S.Normal]
    (hS : S ≤ Subgroup.center G)
    (A : Finset Γ) (hA : ∀ g : G, (∀ a ∈ A, (a : G)*g = g*a) → g ∈ S) :
    DiscreteTopology (Γ.map (QuotientGroup.mk' S)) := by
  classical
  let π := QuotientGroup.mk' S
  obtain ⟨V,hVo,hV⟩ := isOpen_induced_iff.mp (isOpen_discrete ({1} : Set Γ))
  have hVone : (1 : G) ∈ V := by
    have hh : (1 : Γ) ∈ (Subtype.val : Γ → G) ⁻¹' V := by rw [hV]; exact Set.mem_singleton _
    exact hh
  have hVG : ∀ g ∈ Γ, g ∈ V → g = 1 := by
    intro g hg hv
    have hh : (⟨g,hg⟩ : Γ) ∈ (Subtype.val : Γ → G) ⁻¹' V := hv
    rw [hV] at hh
    exact congrArg Subtype.val (Set.mem_singleton_iff.mp hh)
  let U : Set G := ⋂ a ∈ A, {g | ⁅(a : G),g⁆ ∈ V}
  have hUo : IsOpen U := by
    apply isOpen_biInter_finset
    intro a ha
    exact hVo.preimage (show Continuous (fun g : G => (a : G)*g*(a : G)⁻¹*g⁻¹) by fun_prop)
  have hUone : (1 : G) ∈ U := by simp only [U,Set.mem_iInter]; intro a ha; simpa using hVone
  rw [discreteTopology_iff_isOpen_singleton_one]
  apply isOpen_induced_iff.mpr
  refine ⟨π '' U,QuotientGroup.isOpenMap_coe U hUo,?_⟩
  ext x
  constructor
  · rintro ⟨u,hu,heu⟩
    obtain ⟨g,hg,hgx⟩ := x.property
    have hep : π u = π g := heu.trans hgx.symm
    let c : G := u⁻¹*g
    have hc : c ∈ S := by
      rw [← QuotientGroup.ker_mk' S]
      change π c = 1
      simp only [c,map_mul,map_inv,hep,inv_mul_cancel]
    have he : g = u*c := by dsimp [c]; group
    have hgs : g ∈ S := by
      apply hA
      intro a ha
      apply commutatorElement_eq_one_iff_mul_comm.mp
      apply hVG
      · exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem a.property hg) (Γ.inv_mem a.property)) (Γ.inv_mem hg)
      · rw [he,commutator_mul_central _ _ _ (hS hc)]
        exact Set.mem_iInter.mp (Set.mem_iInter.mp hu a) ha
    have hπg : π g = 1 := (QuotientGroup.eq_one_iff _).mpr hgs
    exact Set.mem_singleton_iff.mpr (Subtype.ext (hgx.symm.trans hπg))
  · intro hx
    have hx1 : x = 1 := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨1,hUone,map_one π⟩

end RawLatticeProjection

namespace RawLatticeFiber

lemma compact_surjecting_set {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [WeaklyLocallyCompactSpace X] [CompactSpace Y]
    (f : X → Y) (hf : IsOpenMap f) (hs : Surjective f) :
    ∃ K : Set X, IsCompact K ∧ f '' K = Set.univ := by
  classical
  choose r hr using hs
  choose K hKc hKr using fun y : Y => exists_compact_mem_nhds (r y)
  have hn (y : Y) : f '' K y ∈ nhds y := by
    simpa only [hr y] using hf.image_mem_nhds (hKr y)
  obtain ⟨A,hA,hcover⟩ := isCompact_univ.elim_nhds_subcover (fun y => f '' K y) (fun y _ => hn y)
  refine ⟨⋃ y ∈ A, K y,A.isCompact_biUnion (fun y _ => hKc y),?_⟩
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨z,hz,k,hk,hky⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_univ y))
  exact ⟨k,Set.mem_iUnion₂.mpr ⟨z,hz,hk⟩,hky⟩

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

 

omit [T2Space G] in
theorem compact_fiber [WeaklyLocallyCompactSpace G]
    (Γ S : Subgroup G) [S.Normal] [CompactSpace (G ⧸ Γ)]
    (hS : IsClosed (S : Set G)) [DiscreteTopology (Γ.map (QuotientGroup.mk' S))] :
    CompactSpace (S ⧸ (Γ.comap S.subtype)) := by
  classical
  let : IsClosed (S : Set G) := hS
  let π := QuotientGroup.mk' S
  let P := Γ.map π
  obtain ⟨K,hK,hKcover⟩ := compact_surjecting_set
    (QuotientGroup.mk : G → G ⧸ Γ) QuotientGroup.isOpenMap_coe QuotientGroup.mk_surjective
  let T : Set (G ⧸ S) := (π '' K) ∩ P
  have hPc : IsClosed (P : Set (G ⧸ S)) := Subgroup.isClosed_of_discreteTopology
  have hTc : IsCompact T := (hK.image (QuotientGroup.continuous_mk)).inter_right hPc
  have hTd : IsDiscrete T := (show IsDiscrete (P : Set (G ⧸ S)) from
    SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance).mono Set.inter_subset_right
  have hTf : T.Finite := hTc.finite hTd
  have hex (q : T) : ∃ g : G, g ∈ Γ ∧ π g = q.val := q.property.2
  choose a haΓ hap using hex
  let B : Set G := ⋃ q : T, (fun k : G => k * (a q)⁻¹) '' K
  let : Fintype T := hTf.fintype
  have hBc : IsCompact B := isCompact_iUnion (fun q => hK.image (continuous_id.mul continuous_const))
  let D : Set S := (Subtype.val : S → G) ⁻¹' B
  have hDc : IsCompact D := hS.isClosedEmbedding_subtypeVal.isCompact_preimage hBc
  have hDcover : (QuotientGroup.mk : S → S ⧸ Γ.comap S.subtype) '' D = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨s,rfl⟩ := QuotientGroup.mk_surjective x
    have hkexist : (QuotientGroup.mk s.val : G ⧸ Γ) ∈ (QuotientGroup.mk : G → G ⧸ Γ) '' K := by
      rw [hKcover]; exact Set.mem_univ _
    obtain ⟨k,hk,hks⟩ := hkexist
    have hγ : k⁻¹*s.val ∈ Γ := QuotientGroup.eq.mp hks
    have hpk : π k ∈ P := by
      refine ⟨(k⁻¹*s.val)⁻¹,Γ.inv_mem hγ,?_⟩
      have hps : π s.val = 1 := (QuotientGroup.eq_one_iff s.val).mpr s.property
      simp only [map_inv,map_mul,hps,mul_one,inv_inv]
    let q : T := ⟨π k,⟨⟨k,hk,rfl⟩,hpk⟩⟩
    let c : G := k*(a q)⁻¹
    have hcS : c ∈ S := by
      apply (QuotientGroup.eq_one_iff c).mp
      change π c = 1
      simp only [c,map_mul,map_inv,hap q,mul_inv_cancel,q]
    refine ⟨⟨c,hcS⟩,?_,?_⟩
    · exact Set.mem_iUnion.mpr ⟨q,⟨k,hk,rfl⟩⟩
    · apply QuotientGroup.eq.mpr
      change c⁻¹*s.val ∈ Γ
      have he : c⁻¹*s.val = a q*(k⁻¹*s.val) := by dsimp [c]; group
      rw [he]
      exact Γ.mul_mem (haΓ q) hγ
  exact ⟨hDcover ▸ hDc.image QuotientGroup.continuous_mk⟩

end RawLatticeFiber

noncomputable section
open Set Function Topology
namespace RawLatticeFiber
variable {G Q : Type*} [Group G] [Group Q] [TopologicalSpace G] [TopologicalSpace Q]

lemma compact_quotient_image (Γ : Subgroup G) [CompactSpace (G ⧸ Γ)]
    (π : G →* Q) (hc : Continuous π) (hs : Surjective π) :
    CompactSpace (Q ⧸ Γ.map π) := by
  let F : G ⧸ Γ → Q ⧸ Γ.map π := Quotient.lift
    (fun g : G => QuotientGroup.mk (π g)) (by
      intro x y hxy
      apply QuotientGroup.eq.mpr
      exact ⟨x⁻¹*y,QuotientGroup.leftRel_apply.mp hxy,by simp only [map_mul,map_inv]⟩)
  have hF : Continuous F := by
    apply (QuotientGroup.isQuotientMap_mk Γ).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp hc
  have hFs : Surjective F := by
    intro x
    obtain ⟨q,rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g,rfl⟩ := hs q
    exact ⟨QuotientGroup.mk g,rfl⟩
  exact hFs.compactSpace hF
end RawLatticeFiber

namespace RawLatticeFiber
open scoped Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [WeaklyLocallyCompactSpace G]

 

theorem discrete_quotient_of_compact_kernel (Γ S : Subgroup G) [DiscreteTopology Γ]
    [S.Normal] [IsClosed (S : Set G)] [WeaklyLocallyCompactSpace S]
    [CompactSpace (S ⧸ Γ.comap S.subtype)] :
    DiscreteTopology (Γ.map (QuotientGroup.mk' S)) := by
  classical
  let π := QuotientGroup.mk' S
  let Λ := Γ.comap S.subtype
  obtain ⟨K,hK,hcover⟩ := compact_surjecting_set (QuotientGroup.mk (s := Λ))
    QuotientGroup.isOpenMap_coe QuotientGroup.mk_surjective
  obtain ⟨V,hV,hVn⟩ := exists_compact_mem_nhds (1 : G)
  have hV1 : (1 : G) ∈ interior V := mem_interior_iff_mem_nhds.mpr hVn
  let A : Set Γ := (Subtype.val : Γ → G) ⁻¹' (V * (Subtype.val '' K))
  have hA : A.Finite := isCompact_iff_finite.mp
    ((Subgroup.isClosed_of_discreteTopology (U := Γ)).isClosedEmbedding_subtypeVal.isCompact_preimage
      (hV.mul (hK.image continuous_subtype_val)))
  let D : Set (G ⧸ S) := (fun γ : Γ => π γ) '' A \ {1}
  have hD : IsClosed D := (hA.image _).sdiff.isClosed
  let O : Set (G ⧸ S) := π '' interior V \ D
  have hO : IsOpen O := (QuotientGroup.isOpenMap_coe _ isOpen_interior).sdiff hD
  have hO1 : (1 : G ⧸ S) ∈ O := ⟨⟨1,hV1,map_one π⟩,by simp [D]⟩
  have reduce (γ : Γ) (u : G) (hu : u ∈ interior V) (hπ : π u = π γ) :
      π γ ∈ (fun γ : Γ => π γ) '' A := by
    let s : S := ⟨u⁻¹ * γ,by
      rw [← QuotientGroup.ker_mk' S]
      change π (u⁻¹ * γ) = 1
      rw [map_mul,map_inv,hπ,inv_mul_cancel]⟩
    have hcs : (QuotientGroup.mk s : S ⧸ Λ) ∈ QuotientGroup.mk '' K := by rw [hcover]; trivial
    obtain ⟨v,hv,hvs⟩ := hcs
    have hval : v⁻¹*s ∈ Λ := QuotientGroup.eq.mp hvs
    let l : Γ := ⟨(v : G)⁻¹ * (s : G),hval⟩
    let γ' : Γ := γ*l⁻¹
    have he : (γ' : G) = u*(v : G) := by
      change (γ : G) * ((v : G)⁻¹*(u⁻¹*γ))⁻¹ = _
      group
    have hlS : (l : G) ∈ S := S.mul_mem (S.inv_mem v.property) s.property
    have hlπ : π (l : G) = 1 := (QuotientGroup.eq_one_iff _).mpr hlS
    refine ⟨γ',?_,?_⟩
    · change (γ' : G) ∈ V * (Subtype.val '' K)
      rw [he]
      exact Set.mul_mem_mul (interior_subset hu) ⟨v,hv,rfl⟩
    · change π ((γ : G)*(l : G)⁻¹) = π γ
      rw [map_mul,map_inv,hlπ,inv_one,mul_one]
  rw [discreteTopology_iff_isOpen_singleton_one]
  apply isOpen_induced_iff.mpr
  refine ⟨O,hO,?_⟩
  ext q
  constructor
  · intro hq
    obtain ⟨u,hu,huq⟩ := hq.1
    obtain ⟨γ,hγ,hγq⟩ := q.property
    have hqa := reduce ⟨γ,hγ⟩ u hu (huq.trans hγq.symm)
    have hqe : (q : G ⧸ S) = 1 := by
      by_contra hn
      apply hq.2
      exact ⟨hγq ▸ hqa,hn⟩
    exact Set.mem_singleton_iff.mpr (Subtype.ext hqe)
  · intro hq
    have he : q = 1 := Set.mem_singleton_iff.mp hq
    subst q
    exact hO1
end RawLatticeFiber
end

end

end OAI
