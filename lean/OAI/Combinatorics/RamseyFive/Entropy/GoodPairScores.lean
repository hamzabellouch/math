import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.CollisionSampling

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
lemma pair_entropy_swap (p : Law X) (f : X→Y) (g : X→Z) :
    entropy (pair p f g)=entropy (pair p g f) := by
  have h:=entropy_map_injective (pair p f g) Prod.swap (by
    intro x y he
    exact Prod.swap_injective he)
  simp only [pair,map_comp,Function.comp_def,Prod.swap_prod_mk] at h
  exact h.symm

variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]

local instance goodPairIndexDecEq : DecidableEq ((B×A)⊕T) := Classical.decEq _

attribute [local irreducible] indexInformation indexCollision indexBad coordinateInformation

def OtherBlock : ((B×A)⊕T)→B→Prop :=
  Sum.elim (fun z b=>b≠z.1) (fun _ _=>True)

omit [Nonempty A] in
lemma index_information_pair (p : Law (((B×A)⊕T)→β)) (s : B→A)
    (i : ((B×A)⊕T)) (b : B) (hi : OtherBlock i b) :
    entropy (map p (fun x=>x i))+entropy (map p (fun x=>x (Sum.inl (b,s b))))-
      entropy (pair p (fun x=>x i) (fun x=>x (Sum.inl (b,s b))))≤ indexInformation p s i := by
  have he : (coordinateInformation p i (Sum.inl (b,s b)):ℝ)=
      entropy (map p (fun x=>x i))+entropy (map p (fun x=>x (Sum.inl (b,s b))))-
        entropy (pair p (fun x=>x i) (fun x=>x (Sum.inl (b,s b)))) := by
    unfold coordinateInformation
    change information (pair p (fun x=>x (Sum.inl (b,s b))) (fun x=>x i))=_
    simp only [information,first_pair,second_pair]
    rw [pair_entropy_swap p (fun x=>x (Sum.inl (b,s b))) (fun x=>x i),add_comm]
  rw [←he]
  cases i with
  | inl z =>
    unfold indexInformation
    change (coordinateInformation p (Sum.inl z) (Sum.inl (b,s b)):ℝ)≤(blockInformation p s z.1 z.2:ℝ)
    apply NNReal.coe_le_coe.mpr
    exact Finset.le_sup (f:=fun c=>coordinateInformation p (Sum.inl z) (Sum.inl (c,s c)))
      (Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩)
  | inr t =>
    unfold indexInformation
    change (coordinateInformation p (Sum.inr t) (Sum.inl (b,s b)):ℝ)≤(middleInformation p s t:ℝ)
    apply NNReal.coe_le_coe.mpr
    exact Finset.le_sup (f:=fun c=>coordinateInformation p (Sum.inr t) (Sum.inl (c,s c)))
      (Finset.mem_univ b)

omit [Fintype A] [Fintype T] [Nonempty A] in
lemma index_collision_pair (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ)
    (hc : ∀ i j,0≤c i j) (s : B→A) (i : ((B×A)⊕T)) (b : B) (hi : OtherBlock i b) :
    c i (Sum.inl (b,s b))≤ indexCollision c s i := by
  cases i with
  | inl z =>
    unfold indexCollision otherCollision
    exact Finset.single_le_sum (f:=fun j=>c (Sum.inl z) (Sum.inl (j,s j))) (fun j _=>hc _ _) (Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩)
  | inr t =>
    unfold indexCollision middleCollision
    exact Finset.single_le_sum (f:=fun j=>c (Sum.inr t) (Sum.inl (j,s j))) (fun j _=>hc _ _) (Finset.mem_univ b)

omit [Nonempty A] in
theorem good_index_scores (J d e : ℝ) (p : Law (((B×A)⊕T)→β))
    (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (hc : ∀ i j,0≤c i j)
    (s : B→A) (i : ((B×A)⊕T)) (hg : indexBad J d e p c s i=0) :
    J-entropy (map p (fun x=>x i))≤d ∧ ∀ b,OtherBlock i b→
      entropy (map p (fun x=>x i))+entropy (map p (fun x=>x (Sum.inl (b,s b))))-
        entropy (pair p (fun x=>x i) (fun x=>x (Sum.inl (b,s b))))+c i (Sum.inl (b,s b))≤e := by
  unfold indexBad at hg
  obtain ⟨hd,he⟩:=badIndexIndicator_eq_zero hg
  refine ⟨hd,fun b hi=>?_⟩
  exact (add_le_add (index_information_pair p s i b hi) (index_collision_pair c hc s i b hi)).trans he

omit [Nonempty A] in
lemma good_index_scores_reverse (J d e : ℝ) (p : Law (((B×A)⊕T)→β))
    (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (hc : ∀ i j,0≤c i j) (hcs : ∀ i j,c i j=c j i)
    (s : B→A) (i : ((B×A)⊕T)) (hg : indexBad J d e p c s i=0)
    (b : B) (hi : OtherBlock i b) :
      entropy (map p (fun x=>x (Sum.inl (b,s b))))+entropy (map p (fun x=>x i))-
        entropy (pair p (fun x=>x (Sum.inl (b,s b))) (fun x=>x i))+c (Sum.inl (b,s b)) i≤e := by
  rw [pair_entropy_swap p (fun x=>x (Sum.inl (b,s b))) (fun x=>x i),hcs (Sum.inl (b,s b)) i,add_comm
    (entropy (map p (fun x=>x (Sum.inl (b,s b)))))]
  exact (good_index_scores J d e p c hc s i hg).2 b hi

end
end SharpRamseyFive.FiniteEntropy

end OAI
