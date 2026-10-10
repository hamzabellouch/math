import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.PreparedGeometry

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*}

lemma own_inter_right (S T : Finset α) (U : β→Finset α) (bs : List β) (x : α) :
    own (S∩T) U bs x=own S U bs x∩T := by
  induction bs generalizing S with
  | nil => simp [own]
  | cons b bs ih =>
    simp only [own]
    split_ifs with hx
    · ext y; simp only [mem_inter]; tauto
    · rw [←sdiff_inter_right_comm,ih]

lemma own_removed (S : Finset α) (U : β→Finset α) (bs : List β) (x : α) :
    own (removed S U bs) U bs x=own S U bs x := by
  rw [removed_eq,own_inter_right]
  apply inter_eq_left.mpr
  have hh := own_subset_removed S U bs x
  rw [removed_eq] at hh
  exact hh.trans inter_subset_right

lemma residual_inter (S T : Finset α) (U : β→Finset α) (bs : List β) :
    residual (S∩T) U bs=residual S U bs∩T := by
  rw [residual_eq,residual_eq]
  exact (sdiff_inter_right_comm _ _ _).symm

lemma indexedCell_inter (S T : Finset α) (U : β→Finset α) (bs : List β) (i : Fin bs.length) :
    indexedCell (S∩T) U bs i=indexedCell S U bs i∩T := by
  simp only [indexedCell,residual_inter]
  ext y; simp only [mem_inter]; tauto

lemma indexedCell_removed (S : Finset α) (U : β→Finset α) (bs : List β) (i : Fin bs.length) :
    indexedCell (removed S U bs) U bs i=indexedCell S U bs i := by
  rw [removed_eq,indexedCell_inter]
  apply inter_eq_left.mpr
  have hh : indexedCell S U bs i⊆removed S U bs := by
    apply cell_subset_removed
    rw [indexedCell_eq]
    exact List.getElem_mem _
  rw [removed_eq] at hh
  exact hh.trans inter_subset_right

end
end SharpLogRamsey.GreedyPreparation

end

end OAI
