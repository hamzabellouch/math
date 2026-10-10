import OAI.Computability.MatchingCount.TerminalMincut

namespace OAI

section

namespace BinaryMatching.OddCutParity
open Finset UnitFlow CutAlgebra TerminalMincut
variable {n : ℕ}

def OddSide (U S : Finset (Fin n)) : Prop := Odd (S∩U).card
instance oddSideDecidable (U S : Finset (Fin n)) : Decidable (OddSide U S) :=
  inferInstanceAs (Decidable (Odd _))

lemma terminal_partition (U A : Finset (Fin n)) :
    (A∩U).card + (Aᶜ∩U).card=U.card := by
  simpa only [sdiff_eq_inter_compl,inter_comm] using card_inter_add_card_sdiff U A

lemma even_other (U A : Finset (Fin n)) (hU : Even U.card) (hA : Even (A∩U).card) :
    Even (Aᶜ∩U).card := by
  have hh := terminal_partition U A
  rw [Nat.even_iff] at hU hA ⊢
  omega

lemma odd_other (U A : Finset (Fin n)) (hU : Even U.card) (hA : OddSide U A) :
    OddSide U Aᶜ := by
  have hh := terminal_partition U A
  rw [Nat.even_iff] at hU
  change Odd (A∩U).card at hA
  change Odd (Aᶜ∩U).card
  rw [Nat.odd_iff] at hA ⊢
  omega

lemma odd_separates (U S : Finset (Fin n)) (hU : Even U.card) (hS : OddSide U S) :
    Separates U S := by
  have hc := odd_other U S hU hS
  have hp : 0<(S∩U).card := by have := Nat.odd_iff.mp hS; omega
  have hpc : 0<(Sᶜ∩U).card := by have := Nat.odd_iff.mp hc; omega
  obtain ⟨a,ha⟩ := card_pos.mp hp
  obtain ⟨z,hz⟩ := card_pos.mp hpc
  exact ⟨a,(mem_inter.mp ha).2,z,(mem_inter.mp hz).2,
    (mem_inter.mp ha).1,mem_compl.mp (mem_inter.mp hz).1⟩

lemma separate_cards (U A : Finset (Fin n)) (hA : Separates U A) :
    0<(A∩U).card ∧ 0<(Aᶜ∩U).card := by
  obtain ⟨a,ha,z,hz,haa,hza⟩ := hA
  exact ⟨card_pos.mpr ⟨a,mem_inter.mpr ⟨haa,ha⟩⟩,
    card_pos.mpr ⟨z,mem_inter.mpr ⟨mem_compl.mpr hza,hz⟩⟩⟩

lemma split_odd (U S A : Finset (Fin n)) (hS : OddSide U S)
    (hnot : ¬OddSide (A∩U) S) : OddSide (Aᶜ∩U) S := by
  have hh := terminal_partition (S∩U) A
  have h₁ : A∩(S∩U)=S∩(A∩U) := by ext v; simp; tauto
  have h₂ : Aᶜ∩(S∩U)=S∩(Aᶜ∩U) := by ext v; simp; tauto
  rw [h₁,h₂] at hh
  simp only [OddSide,Nat.odd_iff] at hS hnot ⊢
  omega

def contractMap (A : Finset (Fin n)) (r : Fin n) (v : Fin n) : Fin n :=
  if v∈A then v else r

lemma lift_contract (A T : Finset (Fin n)) (r : Fin n) :
    lift (contractMap A r) T = if r∈T then (T∩A)∪Aᶜ else T∩A := by
  ext v
  by_cases hv : v∈A <;> by_cases hr : r∈T <;>
    simp [mem_lift,contractMap,hv,hr]

lemma lift_card (U A T : Finset (Fin n)) (r : Fin n) :
    (lift (contractMap A r) T∩U).card =
      (T∩(A∩U)).card + if r∈T then (Aᶜ∩U).card else 0 := by
  rw [lift_contract]
  split_ifs with hr
  · have hd : Disjoint ((T∩A)∩U) (Aᶜ∩U) := by
      apply disjoint_left.mpr
      intro v hv hw
      exact (mem_compl.mp (mem_inter.mp hw).1) (mem_inter.mp (mem_inter.mp hv).1).2
    rw [union_inter_distrib_right,card_union_of_disjoint hd]
    rw [inter_assoc]
  · simp only [inter_assoc,add_zero]

lemma odd_lift_iff (U A T : Finset (Fin n)) (r : Fin n)
    (he : Even (Aᶜ∩U).card) :
    OddSide U (lift (contractMap A r) T) ↔ OddSide (A∩U) T := by
  simp only [OddSide,lift_card,Nat.odd_iff]
  rw [Nat.even_iff] at he
  split_ifs <;> omega

lemma lift_of_subset (A T : Finset (Fin n)) (r : Fin n) (hr : r∉A) (hT : T⊆A) :
    lift (contractMap A r) T=T := by
  have hrt : r∉T := fun h => hr (hT h)
  rw [lift_contract,ite_eq_right hrt,inter_eq_left.mpr hT]

lemma cut_contract_subset (c : Fin n → Fin n → ℕ) (A T : Finset (Fin n))
    (r : Fin n) (hr : r∉A) (hT : T⊆A) :
    cutCapacity (push c (contractMap A r)) T=cutCapacity c T := by
  rw [cut_push,lift_of_subset A T r hr hT]

lemma odd_subset_iff (U A T : Finset (Fin n)) (hT : T⊆A) :
    OddSide (A∩U) T ↔ OddSide U T := by
  have hh : T∩(A∩U)=T∩U := by rw [←inter_assoc,inter_eq_left.mpr hT]
  rw [OddSide,OddSide,hh]

end BinaryMatching.OddCutParity
end

end OAI
