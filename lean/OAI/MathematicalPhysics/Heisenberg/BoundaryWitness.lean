import OAI.MathematicalPhysics.Heisenberg.TwoEndedReturns

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.LayeredExchange
variable {V : Type*} [Fintype V]

lemma cycle_boundary_witness (π : Equiv.Perm V) (B C : Set V)
    (hC : ∀ z,∃ n : ℕ,(π^n) z∈C) {z : V} (hz : z∈B) :
    ∃ w,π.SameCycle z w ∧ w∈B ∧ (w∈C ∨ π w∉B) := by
  by_contra hn
  have hn' : ∀ w,π.SameCycle z w → w∈B → w∉C ∧ π w∈B := by
    intro w hw hB
    constructor
    · intro hc; exact hn ⟨w,hw,hB,Or.inl hc⟩
    · by_contra hb; exact hn ⟨w,hw,hB,Or.inr hb⟩
  have hb : ∀ n : ℕ,(π^n) z∈B := by
    intro n
    induction n with
    | zero => exact hz
    | succ n ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      exact (hn' _ ((Equiv.Perm.SameCycle.refl π z).pow_right (n:=n)) ih).2
  obtain ⟨n,hnC⟩:=hC z
  exact (hn' _ ((Equiv.Perm.SameCycle.refl π z).pow_right (n:=n)) (hb n)).1 hnC

local instance (π : Equiv.Perm V) : Fintype (Classes π) := Fintype.ofFinite _

def hitClasses (π : Equiv.Perm V) (B : Set V) : Finset (Classes π) :=
  Finset.univ.filter fun c=>∃ z∈B,classOf π z=c

def witnesses (π : Equiv.Perm V) (B C : Set V) : Finset V :=
  Finset.univ.filter fun z=>z∈B ∧ (z∈C ∨ π z∉B)

lemma hitClasses_le_witnesses (π : Equiv.Perm V) (B C : Set V)
    (hC : ∀ z,∃ n : ℕ,(π^n) z∈C) :
    (hitClasses π B).card ≤ (witnesses π B C).card := by
  have hh : hitClasses π B⊆(witnesses π B C).image (classOf π) := by
    intro c hc
    obtain ⟨z,hz,rfl⟩:=(Finset.mem_filter.mp hc).2
    obtain ⟨w,hw,hB,hW⟩:=cycle_boundary_witness π B C hC hz
    refine Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hB,hW⟩,?_⟩
    exact ((classOf_eq_iff π z w).mpr hw).symm
  exact (Finset.card_le_card hh).trans Finset.card_image_le

lemma witness_count (π : Equiv.Perm V) (B C : Set V) :
    (witnesses π B C).card ≤ (Finset.univ.filter fun z=>z∈B∩C).card+
      (Finset.univ.filter fun z=>z∈B ∧ π z∉B).card := by
  apply le_trans (Finset.card_le_card (show witnesses π B C⊆
    (Finset.univ.filter fun z=>z∈B∩C)∪(Finset.univ.filter fun z=>z∈B ∧ π z∉B) from ?_))
    (Finset.card_union_le _ _)
  intro z hz
  rcases (Finset.mem_filter.mp hz).2 with ⟨hb,hc|he⟩
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb,hc⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb,he⟩)

lemma missing_add_hit (π : Equiv.Perm V) (B : Set V) :
    missingCount π B+(hitClasses π B).card=missingCount π ∅ := by
  have hmiss : missingCount π B=(Finset.univ.filter fun c : Classes π=>¬∃ z∈B,classOf π z=c).card := by
    unfold missingCount
    rw [Nat.card_eq_fintype_card]
    convert Fintype.card_subtype (fun c : Classes π=>∀ z∈B,c≠classOf π z) using 1
    congr 1
    ext c
    simp [not_exists,not_and,eq_comm]
  have hempty : missingCount π ∅=Fintype.card (Classes π) := by
    unfold missingCount
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeUnivEquiv (fun _=>by simp))
  rw [hmiss,hempty]
  simpa [not_not,Finset.card_univ,hitClasses] using (Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun c : Classes π=>¬∃ z∈B,classOf π z=c))

end Heisenberg.Surface
end
end

end OAI
