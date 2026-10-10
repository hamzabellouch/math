import Mathlib
import OAI.Probability.BinarySweep.GridBounds.GridSplit
import OAI.Probability.BinarySweep.Trajectories.EndpointEvents

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit

section
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ)

lemma outside_left (j : Fin m) (x : GridSlot bits) :
    (leftOutsideEquiv bits j) (fun i => x i.val) =
      (rightSlot bits x,fun i : {i : Fin m // i≠j} => leftSlot bits x i.val) := rfl
lemma outside_right (j : Fin n) (x : GridSlot bits) :
    (rightOutsideEquiv bits j) (fun i => x i.val) =
      (leftSlot bits x,fun i : {i : Fin n // i≠j} => rightSlot bits x i.val) := rfl

lemma rowChoices_at (g : GridChoices bits) (x : GridSlot bits) (j : Fin m) :
    rowChoices bits g (rightSlot bits x) j (fun i => leftSlot bits x i.val) =
      g (j.castAdd n) (fun i => x i.val) := by
  unfold rowChoices
  rw [← outside_left,Equiv.symm_apply_apply]

lemma columnChoices_at (g : GridChoices bits) (x : GridSlot bits) (j : Fin n) :
    columnChoices bits g (leftSlot bits x) j (fun i => rightSlot bits x i.val) =
      g (j.natAdd m) (fun i => x i.val) := by
  unfold columnChoices
  rw [← outside_right,Equiv.symm_apply_apply]

lemma gridWeight_split (z : ℝ) (g : GridChoices bits) :
    gridWeight bits z g =
      (∏y : GridSlot (rightBits bits), gridWeight (leftBits bits) z (rowChoices bits g y)) *
      (∏x : GridSlot (leftBits bits), gridWeight (rightBits bits) z (columnChoices bits g x)) := by
  unfold gridWeight
  rw [Fin.prod_univ_add]
  congr 1
  · rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    have he := (leftOutsideEquiv bits j).symm.prod_comp (fun u => lineLaw (bits (j.castAdd n)) z (g (j.castAdd n) u))
    rw [Fintype.prod_prod_type] at he
    exact he.symm
  · rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    have he := (rightOutsideEquiv bits j).symm.prod_comp (fun u => lineLaw (bits (j.natAdd m)) z (g (j.natAdd m) u))
    rw [Fintype.prod_prod_type] at he
    exact he.symm

lemma gridLayer_path_iff {b h : ℕ} {a : Fin b → ℕ} (H : PathFamily a h)
    (g : GridChoices a) (j : Fin b) (k : Fin h) :
    gridLayer a g j (H.position j.castSucc k)=H.position j.succ k ↔
      g j (fun i => H.position j.castSucc k i.val) (H.position j.castSucc k j)=H.position j.succ k j := by
  constructor
  · intro he
    have hh := congrFun he j
    rwa [gridLayer_at] at hh
  · intro he
    funext i
    by_cases hi : i=j
    · subst i; exact (gridLayer_at g j _).trans he
    · rw [gridLayer_other a g j i hi,H.changes_only_stage j k i hi]

end

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

lemma row_stage_iff (g : GridChoices bits) (y : GridSlot (rightBits bits))
    (j : Fin m) (a : RowLabels bits H y) :
    gridLayer (leftBits bits) (rowChoices bits g y) j
      ((rowFamily bits H y).position j.castSucc (Fintype.equivFin (RowLabels bits H y) a)) =
      (rowFamily bits H y).position j.succ (Fintype.equivFin (RowLabels bits H y) a) ↔
    gridLayer bits g (j.castAdd n) (H.position (leftTime j.castSucc) a.val) =
      H.position (leftTime j.succ) a.val := by
  change _ ↔ gridLayer bits g (j.castAdd n)
    (H.position (j.castAdd n).castSucc a.val)=H.position (j.castAdd n).succ a.val
  rw [gridLayer_path_iff (rowFamily bits H y),
    gridLayer_path_iff H g (j.castAdd n) a.val]
  simp only [rowFamily,Equiv.symm_apply_apply]
  have hr : rightSlot bits (H.position (leftTime j.castSucc) a.val)=y :=
    (rightSlot_leftTime bits H j.castSucc a.val).trans a.property
  have hc : rowChoices bits g y j
      (fun i => leftSlot bits (H.position (leftTime j.castSucc) a.val) i.val) =
      g (j.castAdd n) (fun i => H.position (leftTime j.castSucc) a.val i.val) := by
    simpa only [hr] using rowChoices_at bits g (H.position (leftTime j.castSucc) a.val) j
  rw [hc]
  rfl

lemma column_stage_iff (g : GridChoices bits) (x : GridSlot (leftBits bits))
    (j : Fin n) (a : ColumnLabels bits H x) :
    gridLayer (rightBits bits) (columnChoices bits g x) j
      ((columnFamily bits H x).position j.castSucc (Fintype.equivFin (ColumnLabels bits H x) a)) =
      (columnFamily bits H x).position j.succ (Fintype.equivFin (ColumnLabels bits H x) a) ↔
    gridLayer bits g (j.natAdd m) (H.position (rightTime j.castSucc) a.val) =
      H.position (rightTime j.succ) a.val := by
  change _ ↔ gridLayer bits g (j.natAdd m)
    (H.position (j.natAdd m).castSucc a.val)=H.position (j.natAdd m).succ a.val
  rw [gridLayer_path_iff (columnFamily bits H x),
    gridLayer_path_iff H g (j.natAdd m) a.val]
  simp only [columnFamily,Equiv.symm_apply_apply]
  have hr : leftSlot bits (H.position (rightTime j.castSucc) a.val)=x :=
    (leftSlot_rightTime bits H j.castSucc a.val).trans a.property
  have hc : columnChoices bits g x j
      (fun i => rightSlot bits (H.position (rightTime j.castSucc) a.val) i.val) =
      g (j.natAdd m) (fun i => H.position (rightTime j.castSucc) a.val i.val) := by
    simpa only [hr] using columnChoices_at bits g (H.position (rightTime j.castSucc) a.val) j
  rw [hc]
  rfl

theorem pathEvent_split (g : GridChoices bits) :
    pathEvent H g ↔
      (∀y, pathEvent (rowFamily bits H y) (rowChoices bits g y)) ∧
      (∀x, pathEvent (columnFamily bits H x) (columnChoices bits g x)) := by
  constructor
  · intro hg
    constructor
    · intro y j k
      obtain ⟨a,rfl⟩ := (Fintype.equivFin (RowLabels bits H y)).surjective k
      exact (row_stage_iff bits H g y j a).mpr (hg _ _)
    · intro x j k
      obtain ⟨a,rfl⟩ := (Fintype.equivFin (ColumnLabels bits H x)).surjective k
      exact (column_stage_iff bits H g x j a).mpr (hg _ _)
  · rintro ⟨hL,hR⟩ j k
    induction j using Fin.addCases with
    | left j =>
      let y := rightSlot bits (H.position 0 k)
      let a : RowLabels bits H y := ⟨k,rfl⟩
      exact (row_stage_iff bits H g y j a).mp (hL y j _)
    | right j =>
      let x := leftSlot bits (H.position (rightTime (m:=m) 0) k)
      let a : ColumnLabels bits H x := ⟨k,rfl⟩
      exact (column_stage_iff bits H g x j a).mp (hR x j _)

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
attribute [local instance] Classical.propDecidable
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

lemma rowChoices_symm (LR : (GridSlot (rightBits bits) → GridChoices (leftBits bits)) ×
    (GridSlot (leftBits bits) → GridChoices (rightBits bits))) :
    rowChoices bits ((choicesEquiv bits).symm LR)=LR.1 :=
  congrArg Prod.fst ((choicesEquiv bits).apply_symm_apply LR)
lemma columnChoices_symm (LR : (GridSlot (rightBits bits) → GridChoices (leftBits bits)) ×
    (GridSlot (leftBits bits) → GridChoices (rightBits bits))) :
    columnChoices bits ((choicesEquiv bits).symm LR)=LR.2 :=
  congrArg Prod.snd ((choicesEquiv bits).apply_symm_apply LR)

lemma eventWeight_split (z : ℝ) (g : GridChoices bits) :
    (if pathEvent H g then gridWeight bits z g else 0) =
      (∏y, if pathEvent (rowFamily bits H y) (rowChoices bits g y) then
        gridWeight (leftBits bits) z (rowChoices bits g y) else 0) *
      (∏x, if pathEvent (columnFamily bits H x) (columnChoices bits g x) then
        gridWeight (rightBits bits) z (columnChoices bits g x) else 0) := by
  classical
  rw [pathEvent_split,gridWeight_split]
  simp only [Fintype.prod_ite_zero]
  split_ifs <;> simp_all

theorem conditionalNormalizer_split (z : ℝ) :
    conditionalNormalizer H z =
      (∏y, conditionalNormalizer (rowFamily bits H y) z) *
      (∏x, conditionalNormalizer (columnFamily bits H x) z) := by
  classical
  let : Fintype (GridChoices (leftBits bits)) := inferInstance
  let : Fintype (GridChoices (rightBits bits)) := inferInstance
  have he := (choicesEquiv bits).symm.sum_comp
    (fun g => if pathEvent H g then gridWeight bits z g else 0)
  have hs (LR : (GridSlot (rightBits bits) → GridChoices (leftBits bits)) ×
      (GridSlot (leftBits bits) → GridChoices (rightBits bits))) :
      (if pathEvent H ((choicesEquiv bits).symm LR) then
        gridWeight bits z ((choicesEquiv bits).symm LR) else 0) =
        (∏y, if pathEvent (rowFamily bits H y) (LR.1 y) then
          gridWeight (leftBits bits) z (LR.1 y) else 0) *
        (∏x, if pathEvent (columnFamily bits H x) (LR.2 x) then
          gridWeight (rightBits bits) z (LR.2 x) else 0) := by
    classical
    rw [eventWeight_split,rowChoices_symm,columnChoices_symm]
  simp_rw [hs] at he
  unfold conditionalNormalizer
  rw [← he,Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  congr 1
  · exact (Fintype.prod_sum (fun (y : GridSlot (rightBits bits)) (g : GridChoices (leftBits bits)) =>
      if pathEvent (rowFamily bits H y) g then gridWeight (leftBits bits) z g else 0)).symm
  · exact (Fintype.prod_sum (fun (x : GridSlot (leftBits bits)) (g : GridChoices (rightBits bits)) =>
      if pathEvent (columnFamily bits H x) g then gridWeight (rightBits bits) z g else 0)).symm

def conditionalChoicesEquiv : ConditionalChoices H ≃
    (∀y, ConditionalChoices (rowFamily bits H y)) ×
    (∀x, ConditionalChoices (columnFamily bits H x)) where
  toFun g := (fun y => ⟨rowChoices bits g.val y,(pathEvent_split bits H g.val).mp g.property |>.1 y⟩,
    fun x => ⟨columnChoices bits g.val x,(pathEvent_split bits H g.val).mp g.property |>.2 x⟩)
  invFun LR := ⟨(choicesEquiv bits).symm (fun y => (LR.1 y).val,fun x => (LR.2 x).val), by
    rw [pathEvent_split,rowChoices_symm,columnChoices_symm]
    exact ⟨fun y => (LR.1 y).property,fun x => (LR.2 x).property⟩⟩
  left_inv g := by
    classical
    apply Subtype.ext
    exact (choicesEquiv bits).symm_apply_apply g.val
  right_inv LR := by
    classical
    apply Prod.ext <;> funext a <;> apply Subtype.ext
    · exact congrFun (rowChoices_symm bits _) a
    · exact congrFun (columnChoices_symm bits _) a

theorem conditionalChoiceWeight_split (z : ℝ) (g : ConditionalChoices H) :
    conditionalChoiceWeight H z g =
      (∏y, conditionalChoiceWeight (rowFamily bits H y) z
        ((conditionalChoicesEquiv bits H g).1 y)) *
      (∏x, conditionalChoiceWeight (columnFamily bits H x) z
        ((conditionalChoicesEquiv bits H g).2 x)) := by
  classical
  unfold conditionalChoiceWeight
  rw [gridWeight_split,conditionalNormalizer_split]
  simp only [Finset.prod_div_distrib,conditionalChoicesEquiv]
  exact mul_div_mul_comm _ _ _ _

end BinaryCoordinateSweeps.GridSplit

end

end OAI
