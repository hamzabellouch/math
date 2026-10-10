import Mathlib

namespace OAI

section
namespace ElementaryPositivity.SquarefreeBlocks
open scoped BigOperators
open Classical
noncomputable section
variable {V:Type*} [DecidableEq V]
variable {n r:ℕ} (b:Fin n ↪ V)

def target : V → ℤ:=∑j:Fin n,Pi.single (b j) 1

def vector (s:Fin r → Finset V) : V → ℤ:=∑i:Fin r,∑x∈s i,Pi.single x 1

lemma target_apply (x:V) : target b x=if x∈Set.range b then 1 else 0 := by
  unfold target
  simp only [Finset.sum_apply,Pi.single_apply]
  by_cases h:x∈Set.range b
  · obtain ⟨j,rfl⟩:=h
    rw [ite_eq_left (Set.mem_range_self j)]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      rw [ite_eq_right (fun h=>hkj (b.injective h.symm))]
    · simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun hj=>h ⟨j,hj.symm⟩)

lemma vector_apply (s:Fin r → Finset V) (x:V) :
    vector s x=((Finset.univ.filter (fun i=>x∈s i)).card:ℤ) := by
  unfold vector
  simp only [Finset.sum_apply,Pi.single_apply]
  simp only [Finset.sum_ite_eq,Finset.sum_boole]

lemma membership_unique (s:Fin r → Finset V) (hs:vector s=target b) (j:Fin n) :
    ∃!i:Fin r,b j∈s i := by
  have H:=congrFun hs (b j)
  rw [vector_apply,target_apply,ite_eq_left (Set.mem_range_self j)] at H
  have hc:(Finset.univ.filter (fun i=>b j∈s i)).card=1:=by exact_mod_cast H
  obtain ⟨i,hi⟩:=Finset.card_eq_one.mp hc
  refine ⟨i,?_,?_⟩
  · have h:i∈Finset.univ.filter (fun i=>b j∈s i):=by rw [hi]; simp
    exact (Finset.mem_filter.mp h).2
  · intro k hk
    have h:k∈Finset.univ.filter (fun i=>b j∈s i):=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩
    rw [hi,Finset.mem_singleton] at h
    exact h

lemma membership_range (s:Fin r → Finset V) (hs:vector s=target b) (i:Fin r) (x:V) (hx:x∈s i) :
    x∈Set.range b := by
  by_contra hn
  have H:=congrFun hs x
  rw [vector_apply,target_apply,ite_eq_right hn] at H
  have hc:(Finset.univ.filter (fun i=>x∈s i)).card=0:=by exact_mod_cast H
  have hh:=Finset.card_eq_zero.mp hc
  have hm:i∈Finset.univ.filter (fun i=>x∈s i):=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩
  rw [hh] at hm
  exact Finset.notMem_empty _ hm

def coloring (s:{s:Fin r → Finset V // vector s=target b}) : Fin n → Fin r:=
  fun j=>(membership_unique b s.val s.property j).choose
lemma coloring_mem (s:{s:Fin r → Finset V // vector s=target b}) (j:Fin n) :
    b j∈s.val (coloring b s j):=(membership_unique b s.val s.property j).choose_spec.1
lemma coloring_eq (s:{s:Fin r → Finset V // vector s=target b}) (j:Fin n) (i:Fin r) (h:b j∈s.val i) :
    coloring b s j=i:=((membership_unique b s.val s.property j).choose_spec.2 i h).symm

def blocks (κ:Fin n → Fin r) (i:Fin r) : Finset V:=
  (Finset.univ.filter (fun j=>κ j=i)).map b
omit [DecidableEq V] in
lemma mem_blocks (κ:Fin n → Fin r) (i:Fin r) (x:V) :
    x∈blocks b κ i ↔ ∃j,κ j=i ∧ b j=x := by simp [blocks]
lemma blocks_vector (κ:Fin n → Fin r) : vector (blocks b κ)=target b := by
  ext x
  simp only [vector,blocks,Finset.sum_apply,Finset.sum_map,Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [ite_apply,Pi.zero_apply]
  change (∑j:Fin n,∑i:Fin r,if κ j=i then (Pi.single (b j) (1:ℤ) : V → ℤ) x else 0)=_
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp only [target,Finset.sum_apply]

def equiv : {s:Fin r → Finset V // vector s=target b} ≃ (Fin n → Fin r) where
  toFun:=coloring b
  invFun κ:=⟨blocks b κ,blocks_vector b κ⟩
  left_inv s:=by
    apply Subtype.ext
    funext i
    apply Finset.ext
    intro x
    rw [mem_blocks]
    constructor
    · rintro ⟨j,hj,rfl⟩
      rw [←hj]
      exact coloring_mem b s j
    · intro hx
      obtain ⟨j,rfl⟩:=membership_range b s.val s.property i x hx
      exact ⟨j,coloring_eq b s j i hx,rfl⟩
  right_inv κ:=by
    funext j
    apply coloring_eq
    exact (mem_blocks b κ (κ j) (b j)).mpr ⟨j,rfl,rfl⟩
end
end ElementaryPositivity.SquarefreeBlocks

end

end OAI
