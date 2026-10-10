import Mathlib
import OAI.Probability.BinarySweep.GridBounds.GridChildAverage

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
open Signed Irrep Representation

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)
  {A : Type*} [Fintype A] [DecidableEq A]

local instance : LinearOrder (GridSlot (rightBits bits)) := rowOrder bits
local instance : LinearOrder (GridSlot (leftBits bits)) := columnOrder bits

def inputToJunction : FreeSlot H 0 ≃ Fin (junctionSize bits H) :=
  (rowReference bits H).trans (junctionEnum bits H)

def junctionTensorRep (p : A → Bool) :
    Representation ℂ (Equiv.Perm (FreeSlot H 0)) (TensorSpace A (junctionSize bits H)) :=
  (hilbertTensorRep p (junctionSize bits H)).comp
    (inputToJunction bits H).permCongrHom.toMonoidHom

def rowChildWeight (z : ℝ) (y : GridSlot (rightBits bits))
    (a : Equiv.Perm (Fin (Fintype.card (FreeSlot (rowFamily bits H y) 0)))) : ℂ :=
  conditionalGroupLaw (rowFamily bits H y) z ((Fintype.equivFin _).symm.permCongr a)

def columnChildWeight (z : ℝ) (x : GridSlot (leftBits bits))
    (a : Equiv.Perm (Fin (Fintype.card (FreeSlot (columnFamily bits H x) 0)))) : ℂ :=
  conditionalGroupLaw (columnFamily bits H x) z ((Fintype.equivFin _).symm.permCongr a)

def rowMatrix (p : A → Bool) (z : ℝ) :=
  groupedAverage (groupingOrder (rowGrouping bits H)) (groupingPerm (rowGrouping bits H)) p
    (rowChildWeight bits H z)

def columnMatrix (p : A → Bool) (z : ℝ) :=
  groupedAverage (groupingOrder (columnGrouping bits H)) (groupingPerm (columnGrouping bits H)) p
    (columnChildWeight bits H z)

lemma row_perm_to_junction (a : ∀y, Equiv.Perm (FreeSlot (rowFamily bits H y) 0)) :
    (inputToJunction bits H).permCongr
      ((rowInputEquiv bits H).symm.permCongr (Equiv.Perm.sigmaCongrRight a))=
      (rowGrouping bits H).permCongr (Equiv.Perm.sigmaCongrRight a) := by
  ext t
  simp [inputToJunction,rowGrouping,Equiv.permCongr_apply]

lemma column_perm_to_junction (a : ∀x, Equiv.Perm (FreeSlot (columnFamily bits H x) 0)) :
    (inputToJunction bits H).permCongr
      ((rowReference bits H).symm.permCongr
        ((columnFreeEquiv bits H 0).symm.permCongr (Equiv.Perm.sigmaCongrRight a)))=
      (columnGrouping bits H).permCongr (Equiv.Perm.sigmaCongrRight a) := by
  ext t
  simp [inputToJunction,columnGrouping,Equiv.permCongr_apply]

lemma rowMatrix_linear (p : A → Bool) (z : ℝ) :
    (rowMatrix bits H p z).toEuclideanLin=
      ∑a : ∀y, Equiv.Perm (FreeSlot (rowFamily bits H y) 0),
        (∏y, (conditionalGroupLaw (rowFamily bits H y) z (a y):ℂ)) •
          hilbertTensorRep p _ ((rowGrouping bits H).permCongr (Equiv.Perm.sigmaCongrRight a)) := by
  refine Eq.trans (groupedAverage_literal_linear (I := GridSlot (rightBits bits))
    (X := fun y => FreeSlot (rowFamily bits H y) 0) (N := junctionSize bits H)
    (A := A) (rowGrouping bits H) p
    (fun y a => (conditionalGroupLaw (rowFamily bits H y) z a : ℂ))) ?_
  apply Finset.sum_congr
  · ext a; simp only [Finset.mem_univ]
  · intro a _; rfl

lemma columnMatrix_linear (p : A → Bool) (z : ℝ) :
    (columnMatrix bits H p z).toEuclideanLin=
      ∑a : ∀x, Equiv.Perm (FreeSlot (columnFamily bits H x) 0),
        (∏x, (conditionalGroupLaw (columnFamily bits H x) z (a x):ℂ)) •
          hilbertTensorRep p _ ((columnGrouping bits H).permCongr (Equiv.Perm.sigmaCongrRight a)) := by
  refine Eq.trans (groupedAverage_literal_linear (I := GridSlot (leftBits bits))
    (X := fun x => FreeSlot (columnFamily bits H x) 0) (N := junctionSize bits H)
    (A := A) (columnGrouping bits H) p
    (fun x a => (conditionalGroupLaw (columnFamily bits H x) z a : ℂ))) ?_
  apply Finset.sum_congr
  · ext a; simp only [Finset.mem_univ]
  · intro a _; rfl

theorem rowAverage_matrix (p : A → Bool) (z : ℝ) :
    rowAverage bits H (junctionTensorRep bits H p) z=(rowMatrix bits H p z).toEuclideanLin := by
  rw [rowAverage_child_laws,rowMatrix_linear]
  apply Finset.sum_congr
  · ext a; simp only [Finset.mem_univ]
  intro a _
  congr 1

theorem columnAverage_matrix (p : A → Bool) (z : ℝ) :
    columnAverage bits H (junctionTensorRep bits H p) z=(columnMatrix bits H p z).toEuclideanLin := by
  rw [columnAverage_child_laws,columnMatrix_linear]
  apply Finset.sum_congr
  · ext a; simp only [Finset.mem_univ]
  intro a _
  congr 1
  change hilbertTensorRep p _ ((inputToJunction bits H).permCongr _) = _
  rw [column_perm_to_junction]

end BinaryCoordinateSweeps.GridSplit

end

end OAI
