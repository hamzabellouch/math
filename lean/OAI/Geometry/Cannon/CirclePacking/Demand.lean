import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleCuts
open Finset

variable {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]

def demand (out : Finset V) (v : V) : ℕ := if v∈out then 1 else 6
omit [Fintype V] in
lemma demand_pos (out : Finset V) (v : V) : 0<demand out v := by
  unfold demand
  split_ifs <;> omega
omit [Fintype V] in
lemma demand_sum (out T : Finset V) :
    (∑ v∈T,demand out v)+5*(T.filter fun v=>v∈out).card=6*T.card := by
  have h (v : V) : demand out v+5*(if v∈out then 1 else 0)=6 := by
    unfold demand
    split_ifs <;> omega
  calc
    _=∑ v∈T,(demand out v+5*(if v∈out then 1 else 0)) := by
      rw [sum_add_distrib,←mul_sum]
      simp [Finset.filter_mem_eq_inter]
    _=6*T.card := by simp_rw [h]; simp [mul_comm]

theorem disk_demands (corners : F → Finset V) (out : F)
    (hout : (corners out).card=3)
    (hEuler : Fintype.card F+4=2*Fintype.card V)
    (hbound : ∀ T : Finset V,T≠Finset.univ →
      (∃ f,corners f⊆T) → (Finset.univ.filter fun f=>corners f⊆T).card+5≤2*T.card) :
    (∑ v,demand (corners out) v)=3*Fintype.card {f : F // f≠out} ∧
    ∀ S : Finset V,S.Nonempty → S≠Finset.univ →
      (∑ v∈S,demand (corners out) v)<
        3*(Finset.univ.filter fun f : {f : F // f≠out}=>∃ v∈S,v∈corners f.val).card := by
  classical
  let A := {f : F // f≠out}
  have hAc : Fintype.card A+1=Fintype.card F := by
    have he : Fintype.card A=(Finset.univ.erase out : Finset F).card :=
      Fintype.card_of_subtype _ (fun _=>by simp)
    rw [he,card_erase_add_one (mem_univ out),card_univ]
  have hsum := demand_sum (corners out) (Finset.univ : Finset V)
  have hfilter : (Finset.univ.filter fun v=>v∈corners out)=corners out := by ext v; simp
  rw [hfilter,hout,card_univ] at hsum
  have htotal : (∑ v,demand (corners out) v)=3*Fintype.card A := by omega
  refine ⟨htotal,?_⟩
  intro S hS hSp
  let T := Sᶜ
  let B : Finset F := Finset.univ.filter (fun f=>corners f⊆T)
  let B' : Finset A := Finset.univ.filter (fun f=>corners f.val⊆T)
  let N : Finset A := Finset.univ.filter (fun f=>∃ v∈S,v∈corners f.val)
  have hTp : T≠Finset.univ := by
    obtain ⟨v,hv⟩ := hS
    intro he
    have ht : v∈T := he ▸ mem_univ v
    exact (mem_compl.mp ht) hv
  have hT : T.Nonempty := by
    by_contra hn
    have he : T=∅ := not_nonempty_iff_eq_empty.mp hn
    apply hSp
    ext v
    simp only [mem_univ,iff_true]
    by_contra hv
    have ht : v∈T := mem_compl.mpr hv
    simp only [he,notMem_empty] at ht
  have hBN : B'.card+N.card=Fintype.card A := by
    have he : N=Finset.univ.filter (fun f : A=>¬corners f.val⊆T) := by
      ext f
      simp only [N,mem_filter,mem_univ,true_and,not_subset]
      constructor
      · rintro ⟨v,hvS,hvf⟩
        exact ⟨v,hvf,fun hvT=>(mem_compl.mp hvT) hvS⟩
      · rintro ⟨v,hvf,hvT⟩
        exact ⟨v,by simpa only [T,mem_compl,not_not] using hvT,hvf⟩
    rw [he]
    exact (card_filter_add_card_filter_not (s:=Finset.univ) (fun f : A=>corners f.val⊆T)).trans (card_univ)
  have himage : B'.image (fun f : A=>f.val)=B.erase out := by
    ext f
    simp only [mem_image,mem_filter,mem_univ,true_and,mem_erase,B',B]
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact ⟨g.property,hg⟩
    · rintro ⟨hf,hB⟩
      exact ⟨⟨f,hf⟩,hB,rfl⟩
  have hBcard : B'.card=(B.erase out).card := by
    rw [←himage,card_image_of_injective _ Subtype.val_injective]
  have hsplit : (∑ v∈S,demand (corners out) v)+(∑ v∈T,demand (corners out) v)=
      ∑ v,demand (corners out) v := sum_add_sum_compl S _
  have hstrict : 3*B'.card<(∑ v∈T,demand (corners out) v) := by
    by_cases hb : B.Nonempty
    · obtain ⟨f,hf⟩ := hb
      have hpl := hbound T hTp ⟨f,(mem_filter.mp hf).2⟩
      change B.card+5≤2*T.card at hpl
      have hd := demand_sum (corners out) T
      by_cases ho : corners out⊆T
      · have hB : out∈B := mem_filter.mpr ⟨mem_univ _,ho⟩
        have hbc : B'.card+1=B.card := by rw [hBcard,card_erase_add_one hB]
        have hfi : T.filter (fun v=>v∈corners out)=corners out := by
          ext v
          simp only [mem_filter]
          exact ⟨fun h=>h.2,fun h=>⟨ho h,h⟩⟩
        rw [hfi,hout] at hd
        omega
      · have hB : out∉B := by simpa only [B,mem_filter,mem_univ,true_and] using ho
        have hbc : B'.card=B.card := by rw [hBcard,erase_eq_of_notMem hB]
        have hsmall : (T.filter fun v=>v∈corners out).card<3 := by
          rw [←hout]
          apply card_lt_card
          refine Finset.ssubset_iff_subset_ne.mpr ⟨fun v hv=>(mem_filter.mp hv).2,?_⟩
          intro he
          apply ho
          intro v hv
          exact (mem_filter.mp (he.symm ▸ hv)).1
        omega
    · have hz : B=∅ := not_nonempty_iff_eq_empty.mp hb
      have hz' : B'.card=0 := by rw [hBcard,hz,erase_empty,card_empty]
      rw [hz',mul_zero]
      exact sum_pos (fun v _=>demand_pos _ v) hT
  change (∑ v∈S,demand (corners out) v)<3*N.card
  omega
end CannonTriangleCuts

end
end
end
end

end OAI
