import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedOutputCount
import OAI.Combinatorics.SharpRamsey.Trees.PreparedChronology

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open TreeDecoder BinaryTree ChronologicalTree
lemma population_flatMap {I A B : Type*} (f : I→List (A×B)) (t : BinaryTree I) :
    population f t=(inorder t).flatMap f := by
  induction t with
  | nil => rfl
  | node i l r hl hr => simp [population,inorder,hl,hr]
end SharpLogRamsey.FreshExecution

namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot w (n+k)→β) (t : Fin k)
local instance finDecC (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance indexDecC (z : (model w n k p θ G t).FreshHistory) :
    DecidableEq ((model w n k p θ G t).Index z.1) := Classical.decEq _

abbrev goodMiddle (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (i : Fin w) : Finset (Fin (2*(n+k))) :=
  univ.filter (fun x=>target w n k p θ G t z.1 (i,x)∉bad)

def goodTarget (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (i : Fin w) :
    Fin (goodMiddle w n k p θ G t z bad i).card ↪ (model w n k p θ G t).Index z.1 :=
  { toFun := fun j=>target w n k p θ G t z.1 (i,(goodMiddle w n k p θ G t z bad i).orderEmbOfFin rfl j)
    inj' := by
      intro a b h
      exact ((goodMiddle w n k p θ G t z bad i).orderEmbOfFin rfl).injective
        (congrArg Prod.snd ((target w n k p θ G t z.1).injective h)) }

lemma goodTarget_eq (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (i : Fin w)
    (j : Fin (goodMiddle w n k p θ G t z bad i).card) :
    goodTarget w n k p θ G t z bad i j=target w n k p θ G t z.1
      (i,(goodMiddle w n k p θ G t z bad i).orderEmbOfFin rfl j) := rfl

lemma goodTarget_not_bad (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (i : Fin w)
    (j : Fin (goodMiddle w n k p θ G t z bad i).card) :
    goodTarget w n k p θ G t z bad i j∉bad := by
  exact (mem_filter.mp ((goodMiddle w n k p θ G t z bad i).orderEmbOfFin_mem rfl j)).2

lemma goodTarget_before (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (i : Fin w)
    (a b : Fin (goodMiddle w n k p θ G t z bad i).card) (hab : a<b) :
    position ((model w n k p θ G t).origin z.1 (goodTarget w n k p θ G t z bad i a)) <
      position ((model w n k p θ G t).origin z.1 (goodTarget w n k p θ G t z bad i b)) := by
  simp only [goodTarget_eq,target_origin]
  have h:=((goodMiddle w n k p θ G t z bad i).orderEmbOfFin rfl).strictMono hab
  change i.val*(4*(n+k))+((n+k)+_) < i.val*(4*(n+k))+((n+k)+_)
  exact Nat.add_lt_add_left (Nat.add_lt_add_left h (n+k)) _

lemma goodTarget_before_next (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (i j : Fin w) (hij : i<j)
    (a : Fin (goodMiddle w n k p θ G t z bad i).card)
    (b : Fin (goodMiddle w n k p θ G t z bad j).card) :
    position ((model w n k p θ G t).origin z.1 (goodTarget w n k p θ G t z bad i a)) <
      position ((model w n k p θ G t).origin z.1 (goodTarget w n k p θ G t z bad j b)) := by
  simp only [goodTarget_eq,target_origin]
  exact owner_before_next i j hij _ _ rfl rfl

theorem goodPopulation_pairwise {A B : Type*} (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (live : Finset (Fin w)) (fallback : Fin w)
    (F : (model w n k p θ G t).Index z.1→A×B) (Q : A×B→A×B→Prop)
    (hQ : ∀ i j,position ((model w n k p θ G t).origin z.1 i) <
      position ((model w n k p θ G t).origin z.1 j)→Q (F i) (F j)) :
    (population (fun i=>List.ofFn (fun j=>F (goodTarget w n k p θ G t z bad i j)))
      (liveTree live fallback)).Pairwise Q := by
  rw [population_flatMap,List.pairwise_flatMap]
  constructor
  · intro i hi
    rw [List.pairwise_ofFn]
    exact fun a b hab=>hQ _ _ (goodTarget_before w n k p θ G t z bad i a b hab)
  · apply (liveTree_ordered live fallback).imp
    intro i j hij x hx y hy
    obtain ⟨a,rfl⟩:=List.mem_ofFn.mp hx
    obtain ⟨b,rfl⟩:=List.mem_ofFn.mp hy
    exact hQ _ _ (goodTarget_before_next w n k p θ G t z bad i j hij a b)

lemma goodPopulation_length {A B : Type*} (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (live : Finset (Fin w)) (fallback : Fin w)
    (F : (model w n k p θ G t).Index z.1→A×B) :
    (population (fun i=>List.ofFn (fun j=>F (goodTarget w n k p θ G t z bad i j)))
      (liveTree live fallback)).length=∑ i∈live,(goodMiddle w n k p θ G t z bad i).card := by
  have hh:=population_length_sum (fun i=>List.ofFn (fun j=>F (goodTarget w n k p θ G t z bad i j)))
    _ (liveTree_separated live fallback)
  rw [liveTree_labels] at hh
  simp only [List.length_ofFn] at hh
  exact_mod_cast hh

lemma goodMiddle_card (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (live : Finset (Fin w)) :
    (∑ i∈live,(goodMiddle w n k p θ G t z bad i).card)=
      (goodTargets (target w n k p θ G t z.1) live bad).card := by
  rw [←card_sigma]
  apply card_bij (fun a _=>target w n k p θ G t z.1 (a.1,a.2))
  · intro a ha
    obtain ⟨hi,hx⟩:=mem_sigma.mp ha
    exact mem_sdiff.mpr ⟨mem_map.mpr ⟨(a.1,a.2),mem_product.mpr ⟨hi,mem_univ _⟩,rfl⟩,
      (mem_filter.mp hx).2⟩
  · intro a ha b hb he
    have hh:=(target w n k p θ G t z.1).injective he
    exact Sigma.ext (congrArg Prod.fst hh) (heq_of_eq (congrArg Prod.snd hh))
  · intro a ha
    obtain ⟨ha,hb⟩:=mem_sdiff.mp ha
    obtain ⟨⟨i,x⟩,hx,rfl⟩:=mem_map.mp ha
    exact ⟨⟨i,x⟩,mem_sigma.mpr ⟨(mem_product.mp hx).1,mem_filter.mpr ⟨mem_univ _,hb⟩⟩,rfl⟩

lemma goodPopulation_size (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (live : Finset (Fin w)) :
    (∑ i∈live,(goodMiddle w n k p θ G t z bad i).card)≤w*(2*(n+k)) := by
  calc
    _ ≤ ∑ _i∈live,2*(n+k) := by
      apply sum_le_sum
      intro i hi
      simpa using card_le_univ (goodMiddle w n k p θ G t z bad i)
    _ = live.card*(2*(n+k)) := by simp
    _ ≤ w*(2*(n+k)) := Nat.mul_le_mul_right _ (by simpa using card_le_univ live)

lemma goodPopulation_predeletion (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (lost : Finset (Fin w)) :
    w*(2*(n+k))≤(∑ i∈univ\lost,(goodMiddle w n k p θ G t z bad i).card)+
      bad.card+lost.card*(2*(n+k)) := by
  rw [goodMiddle_card]
  simpa only [Fintype.card_fin] using goodTargets_loss (target w n k p θ G t z.1) lost bad

end
end SharpLogRamsey.Selection.Windows

end

end OAI
