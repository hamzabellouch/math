import Mathlib
import OAI.Probability.BinarySweep.GridBounds.GroupedMoments
import OAI.Probability.BinarySweep.GridBounds.GroupingGeometry
import OAI.Probability.BinarySweep.GridBounds.GridSplitFree
import OAI.Probability.BinarySweep.FiniteLaws.IndependentPush

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

lemma finitePush_conditional {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (a : Equiv.Perm (FreeSlot H 0)) :
    finitePush (fun g : ConditionalChoices H => (conditionalChoiceWeight H z g:ℂ))
      (fun g => remainingPerm H g.val g.property) a = (conditionalGroupLaw H z a:ℂ) := by
  simp only [finitePush,conditionalGroupLaw,Complex.ofReal_sum,apply_ite,Complex.ofReal_zero]

lemma independentConditional_expectation {I : Type*} [Fintype I]
    (b h : I → ℕ) (bits : ∀i, Fin (b i) → ℕ) (H : ∀i, PathFamily (bits i) (h i))
    {V : Type*} [AddCommMonoid V] [Module ℂ V] (z : ℝ)
    (F : (∀i, Equiv.Perm (FreeSlot (H i) 0)) → V) :
    (∑a, (∏i, (conditionalGroupLaw (H i) z (a i):ℂ)) • F a) =
      ∑g : ∀i, ConditionalChoices (H i),
        (∏i, (conditionalChoiceWeight (H i) z (g i):ℂ)) •
          F (fun i => remainingPerm (H i) (g i).val (g i).property) := by
  have he := independentPush_expectation
    (fun i (g : ConditionalChoices (H i)) => (conditionalChoiceWeight (H i) z g:ℂ))
    (fun i (g : ConditionalChoices (H i)) => remainingPerm (H i) g.val g.property) F
  simpa only [finitePush_conditional] using he

private lemma sigma_relative {I X Y : Type*} {A B : I → Type*}
    (e : X ≃ Σ i, A i) (f : Y ≃ Σ i, B i) (g r : ∀ i, A i ≃ B i) :
    (e.trans ((Equiv.sigmaCongrRight g).trans f.symm)).trans
      (e.trans ((Equiv.sigmaCongrRight r).trans f.symm)).symm =
      e.symm.permCongr (Equiv.Perm.sigmaCongrRight (fun i => (g i).trans (r i).symm)) := by
  ext x
  simp [Equiv.permCongr_apply, Equiv.sigmaCongrRight, Equiv.Perm.sigmaCongrRight]

namespace GridSplit
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

def rowInputEquiv : FreeSlot H 0 ≃
    Σy : GridSlot (rightBits bits), FreeSlot (rowFamily bits H y) 0 := rowFreeEquiv bits H 0

lemma rowRelative_sigma (g : RowSamples bits H) :
    rowRelative bits H g = (rowInputEquiv bits H).symm.permCongr
      (Equiv.Perm.sigmaCongrRight (fun y =>
        remainingPerm (rowFamily bits H y) (g y).val (g y).property)) := by
  exact sigma_relative (rowFreeEquiv bits H 0) (rowFreeEquiv bits H (Fin.last m))
    (fun y => remainingBijection (rowFamily bits H y) (g y).val (g y).property)
    (fun y => freeIdentification (rowFamily bits H y))

lemma columnRelative_sigma (g : ColumnSamples bits H) :
    columnRelative bits H g = (columnFreeEquiv bits H 0).symm.permCongr
      (Equiv.Perm.sigmaCongrRight (fun x =>
        remainingPerm (columnFamily bits H x) (g x).val (g x).property)) := by
  exact sigma_relative (columnFreeEquiv bits H 0) (columnFreeEquiv bits H (Fin.last n))
    (fun x => remainingBijection (columnFamily bits H x) (g x).val (g x).property)
    (fun x => freeIdentification (columnFamily bits H x))

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) V)

omit [FiniteDimensional ℂ V] in
theorem rowAverage_child_laws (z : ℝ) :
    rowAverage bits H ρ z =
      ∑a : ∀y, Equiv.Perm (FreeSlot (rowFamily bits H y) 0),
        (∏y, (conditionalGroupLaw (rowFamily bits H y) z (a y):ℂ)) •
          ρ ((rowInputEquiv bits H).symm.permCongr (Equiv.Perm.sigmaCongrRight a)) := by
  trans ∑g : RowSamples bits H,
    (∏y, (conditionalChoiceWeight (rowFamily bits H y) z (g y):ℂ)) •
      ρ ((rowInputEquiv bits H).symm.permCongr (Equiv.Perm.sigmaCongrRight
        (fun y => remainingPerm (rowFamily bits H y) (g y).val (g y).property)))
  · unfold rowAverage
    apply Finset.sum_congr rfl
    intro g _
    rw [rowRelative_sigma]
  · let F : (∀y, Equiv.Perm (FreeSlot (rowFamily bits H y) 0)) → Module.End ℂ V :=
      fun a => ρ ((rowInputEquiv bits H).symm.permCongr (Equiv.Perm.sigmaCongrRight a))
    have he := independentConditional_expectation (I := GridSlot (rightBits bits)) (fun _ => m)
      (fun y => Fintype.card (RowLabels bits H y)) (fun _ => leftBits bits) (rowFamily bits H) z
      F
    apply Eq.symm
    refine Eq.trans ?_ (Eq.trans he ?_)
    all_goals
      apply Finset.sum_congr
      · ext g; simp only [Finset.mem_univ]
      · intro g _; rfl

omit [FiniteDimensional ℂ V] in
theorem columnAverage_child_laws (z : ℝ) :
    columnAverage bits H ρ z =
      ∑a : ∀x, Equiv.Perm (FreeSlot (columnFamily bits H x) 0),
        (∏x, (conditionalGroupLaw (columnFamily bits H x) z (a x):ℂ)) •
          ρ ((rowReference bits H).symm.permCongr
            ((columnFreeEquiv bits H 0).symm.permCongr (Equiv.Perm.sigmaCongrRight a))) := by
  trans ∑g : ColumnSamples bits H,
    (∏x, (conditionalChoiceWeight (columnFamily bits H x) z (g x):ℂ)) •
      ρ ((rowReference bits H).symm.permCongr
        ((columnFreeEquiv bits H 0).symm.permCongr (Equiv.Perm.sigmaCongrRight
          (fun x => remainingPerm (columnFamily bits H x) (g x).val (g x).property))))
  · unfold columnAverage
    apply Finset.sum_congr rfl
    intro g _
    rw [columnRelative_sigma]
  · let F : (∀x, Equiv.Perm (FreeSlot (columnFamily bits H x) 0)) → Module.End ℂ V :=
      fun a => ρ ((rowReference bits H).symm.permCongr
        ((columnFreeEquiv bits H 0).symm.permCongr (Equiv.Perm.sigmaCongrRight a)))
    have he := independentConditional_expectation (I := GridSlot (leftBits bits)) (fun _ => n)
      (fun x => Fintype.card (ColumnLabels bits H x)) (fun _ => rightBits bits) (columnFamily bits H) z
      F
    apply Eq.symm
    refine Eq.trans ?_ (Eq.trans he ?_)
    all_goals
      apply Finset.sum_congr
      · ext g; simp only [Finset.mem_univ]
      · intro g _; rfl

end GridSplit
end BinaryCoordinateSweeps

namespace BinaryCoordinateSweeps.GridSplit
open Signed

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

local instance rowOrder : LinearOrder (GridSlot (rightBits bits)) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
local instance columnOrder : LinearOrder (GridSlot (leftBits bits)) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

abbrev Junction := FreeSlot H (rightTime (m:=m) 0)
abbrev junctionSize := Fintype.card (Junction bits H)

def junctionEnum : Junction bits H ≃ Fin (junctionSize bits H) := Fintype.equivFin _

def physicalBoard : Fin (junctionSize bits H) ↪
    GridSlot (rightBits bits) × GridSlot (leftBits bits) where
  toFun t := (rightSlot bits ((junctionEnum bits H).symm t).val,
    leftSlot bits ((junctionEnum bits H).symm t).val)
  inj' := by
    intro t u he
    apply (junctionEnum bits H).symm.injective
    apply Subtype.ext
    apply (slotEquiv bits).injective
    exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)

def rowGrouping : (Σy : GridSlot (rightBits bits), FreeSlot (rowFamily bits H y) 0) ≃
    Fin (junctionSize bits H) :=
  (rowInputEquiv bits H).symm.trans ((rowReference bits H).trans (junctionEnum bits H))

def columnGrouping : (Σx : GridSlot (leftBits bits), FreeSlot (columnFamily bits H x) 0) ≃
    Fin (junctionSize bits H) :=
  (columnFreeEquiv bits H 0).symm.trans (junctionEnum bits H)

lemma rowReference_right (a : FreeSlot H 0) :
    rightSlot bits (rowReference bits H a).val=rightSlot bits a.val := by
  exact right_join bits _ _

lemma rowGrouping_first (t : Fin (junctionSize bits H)) :
    ((rowGrouping bits H).symm t).1=(physicalBoard bits H t).1 := by
  change rightSlot bits ((rowReference bits H).symm ((junctionEnum bits H).symm t)).val =
    rightSlot bits ((junctionEnum bits H).symm t).val
  symm
  simpa only [Equiv.apply_symm_apply] using
    rowReference_right bits H ((rowReference bits H).symm ((junctionEnum bits H).symm t))

lemma columnGrouping_first (t : Fin (junctionSize bits H)) :
    ((columnGrouping bits H).symm t).1=(physicalBoard bits H t).2 := rfl

lemma physicalBoard_row (t : Fin (junctionSize bits H)) :
    groupOf (groupingOrder (rowGrouping bits H)) (groupingPerm (rowGrouping bits H)) t=
      (physicalBoard bits H t).1 := by
  rw [grouping_groupOf,rowGrouping_first]

lemma physicalBoard_column (t : Fin (junctionSize bits H)) :
    groupOf (groupingOrder (columnGrouping bits H)) (groupingPerm (columnGrouping bits H)) t=
      (physicalBoard bits H t).2 := by
  rw [grouping_groupOf,columnGrouping_first]

lemma junctionSize_eq : junctionSize bits H=gridSize bits-h := by
  exact card_freeSlot H _

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Signed
variable {I A : Type*} [Fintype I] [LinearOrder I] [Fintype A] [DecidableEq A]
  {X : I → Type*} [∀i,Fintype (X i)] {N : ℕ}

def finBlockPermEquiv : (∀i, Equiv.Perm (X i)) ≃
    (∀i, Equiv.Perm (Fin (Fintype.card (X i)))) :=
  Equiv.piCongrRight (fun i => (Fintype.equivFin (X i)).permCongr)

theorem groupedAverage_literal (e : (Σi, X i) ≃ Fin N) (p : A → Bool)
    (w : ∀i, Equiv.Perm (X i) → ℂ) :
    groupedAverage (groupingOrder e) (groupingPerm e) p
      (fun i a => w i ((Fintype.equivFin (X i)).symm.permCongr a)) =
      ∑a : ∀i, Equiv.Perm (X i), (∏i, w i (a i)) •
        actionMatrix p (e.permCongr (Equiv.Perm.sigmaCongrRight a)) := by
  rw [groupedAverage_law,← (finBlockPermEquiv (X:=X)).sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [grouping_permutation]
  have he (i : I) : (Fintype.equivFin (X i)).symm.permCongr
      (finBlockPermEquiv a i)=a i := by
    ext x
    simp [finBlockPermEquiv,Equiv.permCongr_apply]
  simp only [he]
  rfl

lemma groupedAverage_literal_linear (e : (Σi, X i) ≃ Fin N) (p : A → Bool)
    (w : ∀i, Equiv.Perm (X i) → ℂ) :
    (groupedAverage (groupingOrder e) (groupingPerm e) p
      (fun i a => w i ((Fintype.equivFin (X i)).symm.permCongr a))).toEuclideanLin =
      ∑a : ∀i, Equiv.Perm (X i), (∏i, w i (a i)) •
        hilbertTensorRep p N (e.permCongr (Equiv.Perm.sigmaCongrRight a)) := by
  rw [groupedAverage_literal]
  simp only [map_sum,map_smul,actionMatrix_linear]

end BinaryCoordinateSweeps.Signed

end

end OAI
