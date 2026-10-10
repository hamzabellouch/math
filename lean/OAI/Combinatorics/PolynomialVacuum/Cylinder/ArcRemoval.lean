import OAI.Combinatorics.PolynomialVacuum.Cylinder.NoSource

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}
namespace OpenIce
variable (D : Finset (Vertex M)) (q : Edge M →₀ ℤ) (hq : ∀v∈D,LocalIce q v)

noncomputable def pathVertices (a : activeInside D q) (ha : (network D q hq).Source a) : Finset (Vertex M) :=
  (traced (a.val,enter D q hq a) ((network D q hq).pathWord a ha)).toFinset

theorem pathVertices_subset (a : activeInside D q) (ha : (network D q hq).Source a) :
    pathVertices D q hq a ha⊆activeInside D q := by
  intro v hv
  exact (network D q hq).pathWord_inside a ha (List.mem_toFinset.mp hv)

theorem start_mem_path (a : activeInside D q) (ha : (network D q hq).Source a) :
    a.val∈pathVertices D q hq a ha := by
  apply List.mem_toFinset.mpr
  have ht : traced (a.val,enter D q hq a) ((network D q hq).pathWord a ha)=
      List.ofFn (fun j => ((network D q hq).pathSite a ha j).val) :=
    (network D q hq).pathWord_trace a ha
  rw [ht,List.mem_ofFn]
  exact ⟨⟨0,(network D q hq).pathLength_pos a ha⟩,congrArg Subtype.val ((network D q hq).pathSite_start a ha)⟩

theorem arc_on_domain_if (a : activeInside D q) (ha : (network D q hq).Source a)
    (v : Vertex M) (hv : v∈D) (k : Fin 3) :
    orientedFlow (extractedArc D q hq a ha) (v,k)=
      if v∈pathVertices D q hq a ha then orientedFlow q (v,k) else 0 := by
  rw [arc_on_domain D q hq a ha v hv k]
  by_cases hp : v∈pathVertices D q hq a ha
  · rw [ite_eq_left hp]
    have ht : traced (a.val,enter D q hq a) ((network D q hq).pathWord a ha)=
        List.ofFn (fun j => ((network D q hq).pathSite a ha j).val) :=
      (network D q hq).pathWord_trace a ha
    have hm:=List.mem_toFinset.mp hp
    rw [ht,List.mem_ofFn] at hm
    obtain ⟨j,rfl⟩:=hm
    exact ((network D q hq).pathWord_turn_at a ha j k).trans
      (at_slot D q hq ((network D q hq).pathSite a ha j) k).symm
  · rw [ite_eq_right hp]
    exact turnVisit_eq_zero_of_not_mem _ _ _ k (by simpa [pathVertices] using hp)

theorem residual_on_domain (a : activeInside D q) (ha : (network D q hq).Source a)
    (v : Vertex M) (hv : v∈D) (k : Fin 3) :
    orientedFlow (q-extractedArc D q hq a ha) (v,k)=
      if v∈pathVertices D q hq a ha then 0 else orientedFlow q (v,k) := by
  rw [map_sub,Finsupp.sub_apply,arc_on_domain_if D q hq a ha v hv k]
  split_ifs <;> simp

theorem residual_active (a : activeInside D q) (ha : (network D q hq).Source a) :
    activeInside D (q-extractedArc D q hq a ha)=activeInside D q\pathVertices D q hq a ha := by
  ext v
  simp only [activeInside,Finset.mem_inter,Finset.mem_sdiff,mem_activeSites]
  constructor
  · rintro ⟨⟨k,hk⟩,hv⟩
    rw [residual_on_domain D q hq a ha v hv k] at hk
    by_cases hp : v∈pathVertices D q hq a ha
    · simp [hp] at hk
    · exact ⟨⟨⟨k,by simpa [hp] using hk⟩,hv⟩,hp⟩
  · rintro ⟨⟨⟨k,hk⟩,hv⟩,hp⟩
    refine ⟨⟨k,?_⟩,hv⟩
    rw [residual_on_domain D q hq a ha v hv k,ite_eq_right hp]
    exact hk

theorem residual_card_lt (a : activeInside D q) (ha : (network D q hq).Source a) :
    (activeInside D (q-extractedArc D q hq a ha)).card<(activeInside D q).card := by
  rw [residual_active D q hq a ha]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.sdiff_subset,?_⟩
  intro he
  have hm : a.val∈activeInside D q\pathVertices D q hq a ha := he.symm ▸ a.property
  exact (Finset.mem_sdiff.mp hm).2 (start_mem_path D q hq a ha)

theorem extractedArc_supported (a : activeInside D q) (ha : (network D q hq).Source a) :
    SupportedAt D (extractedArc D q hq a ha) := by
  intro g hg hr
  have hh : g.1∉traced (a.val,enter D q hq a) ((network D q hq).pathWord a ha) := by
    intro hh
    exact hg (Finset.mem_inter.mp ((network D q hq).pathWord_inside a ha hh)).2
  have hs : reverseGerm (a.val,enter D q hq a)≠g := by
    intro hs
    apply hr
    rw [← hs,reverseGerm_reverseGerm]
    exact (Finset.mem_inter.mp a.property).2
  have he : terminalGerm (a.val,enter D q hq a) ((network D q hq).pathWord a ha)≠g := by
    have ht : terminalGerm (a.val,enter D q hq a) ((network D q hq).pathWord a ha)=
        (network D q hq).pathEnd a ha := (network D q hq).pathWord_terminal a ha
    rw [ht]
    intro he
    apply hr
    rw [← he]
    simp only [reverseGerm,OpenNetwork.pathEnd,neighbor_neighbor]
    exact (Finset.mem_inter.mp (((network D q hq).pathSite a ha ((network D q hq).pathLast a ha)).property)).2
  rw [extractedArc,orientedFlow_arc]
  have hz :=turnVisit_eq_zero_of_not_mem _ _ g.1 g.2 hh
  simpa [Finsupp.single_apply,hs,he] using hz

theorem residual_supported (hs : SupportedAt D q) (a : activeInside D q)
    (ha : (network D q hq).Source a) : SupportedAt D (q-extractedArc D q hq a ha) := by
  intro g hg hr
  simp only [map_sub,Finsupp.sub_apply,hs g hg hr,extractedArc_supported D q hq a ha g hg hr,sub_self]
end OpenIce
end PolynomialVacuumCylinder

end OAI
