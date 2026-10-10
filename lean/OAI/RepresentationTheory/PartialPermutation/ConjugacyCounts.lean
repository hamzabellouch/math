import Mathlib
import OAI.RepresentationTheory.PartialPermutation.DiagramCounts

namespace OAI

section

namespace PartialPermutation.DiagramCounting
noncomputable section
open Finset
open scoped Classical

lemma cellsOfRowLens_card (w : List ℕ) : (YoungDiagram.cellsOfRowLens w).card=w.sum := by
  induction w with
  | nil => simp [YoungDiagram.cellsOfRowLens]
  | cons a w ih =>
    have hd : Disjoint (({0} : Finset ℕ) ×ˢ range a)
        ((YoungDiagram.cellsOfRowLens w).map
          (Function.Embedding.prodMap ⟨Nat.succ,Nat.succ_injective⟩ (Function.Embedding.refl ℕ))) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨z,hz,he⟩ := mem_map.mp hy
      have hx0 : x.1=0 := by simpa using (mem_product.mp hx).1
      have hh := congrArg Prod.fst he
      change z.1+1=x.1 at hh
      omega
    simp only [YoungDiagram.cellsOfRowLens,card_union_of_disjoint hd,card_product,
      card_singleton,card_range,one_mul,card_map,ih,List.sum_cons]

def partitionShape {n : ℕ} (p : n.Partition) : Shape n :=
  ⟨YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·))
    (List.sortedGE_iff_pairwise.mpr (Multiset.pairwise_sort _ _)),by
    rw [YoungDiagram.ofRowLens,cellsOfRowLens_card]
    have hs := congrArg Multiset.sum (Multiset.sort_eq p.parts (· ≥ ·))
    exact hs.trans p.parts_sum⟩

lemma partitionShape_injective {n : ℕ} : Function.Injective (@partitionShape n) := by
  intro p q h
  have hp : (partitionShape p).1.rowLens=p.parts.sort (· ≥ ·) :=
    YoungDiagram.rowLens_ofRowLens_eq_self (hw := List.sortedGE_iff_pairwise.mpr (Multiset.pairwise_sort _ _)) (fun x hx => p.parts_pos ((Multiset.mem_sort _).mp hx))
  have hq : (partitionShape q).1.rowLens=q.parts.sort (· ≥ ·) :=
    YoungDiagram.rowLens_ofRowLens_eq_self (hw := List.sortedGE_iff_pairwise.mpr (Multiset.pairwise_sort _ _)) (fun x hx => q.parts_pos ((Multiset.mem_sort _).mp hx))
  apply Nat.Partition.ext
  have he := congrArg (fun μ : Shape n => μ.1.rowLens) h
  rw [hp,hq] at he
  exact (Multiset.sort_eq p.parts (· ≥ ·)).symm.trans
    ((congrArg (fun l : List ℕ => (l : Multiset ℕ)) he).trans (Multiset.sort_eq q.parts (· ≥ ·)))

def conjugacyPartition {α : Type*} [Fintype α] [DecidableEq α] :
    ConjClasses (Equiv.Perm α) → (Fintype.card α).Partition :=
  Quotient.lift Equiv.Perm.partition (fun _ _ h => Equiv.Perm.partition_eq_of_isConj.mp h)

lemma conjugacyPartition_injective {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Injective (@conjugacyPartition α _ _) := by
  intro a b
  induction a using Quotient.inductionOn with | _ g =>
    induction b using Quotient.inductionOn with | _ h =>
      intro he
      exact Quotient.sound (Equiv.Perm.partition_eq_of_isConj.mpr he)

lemma symmetric_conjClasses_card_le (n : ℕ) :
    Nat.card (ConjClasses (Equiv.Perm (Fin n))) ≤ Fintype.card (Shape n) := by
  let : Fintype (ConjClasses (Equiv.Perm (Fin n))) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective _
    (partitionShape_injective.comp (@conjugacyPartition_injective (Fin n) _ _))
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using h

end
end PartialPermutation.DiagramCounting

end

end OAI
