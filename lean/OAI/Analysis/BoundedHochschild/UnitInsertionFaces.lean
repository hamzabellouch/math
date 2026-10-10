import OAI.Analysis.BoundedHochschild.CentralHomotopy

namespace OAI

/-! Elementary face formulas for inserting the algebra identity in a
bounded cochain. These are the individual operator identities used by the
finite averaging homotopy. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma curryMid_leftCoboundary_zero {n : ℕ} (f : Cochain M n) :
    (leftCoboundary f).curryMid 0 1 = f := by
  ext x
  change (Fin.insertNth (α := fun _ => M) 0 1 x) 0 *
    f (fun j => (Fin.insertNth (α := fun _ => M) 0 1 x) j.succ) = f x
  simp only [Fin.insertNth_zero', Fin.cons_zero, Fin.cons_succ, one_mul]

lemma curryMid_leftCoboundary_succ {n : ℕ} (f : Cochain M (n + 1))
    (i : Fin (n + 1)) :
    (leftCoboundary f).curryMid i.succ 1 = leftCoboundary (f.curryMid i 1) := by
  ext x
  have h0 : i.succ.insertNth (α := fun _ => M) 1 x 0 = x 0 := by
    rw [tupleInsert_lt _ _ _ _ (by simp)]
    rfl
  have ht : (fun j : Fin (n + 1) => i.succ.insertNth (α := fun _ => M) 1 x j.succ) =
      i.insertNth 1 (Fin.tail x) := by
    apply (Fin.eq_insertNth_iff).mpr
    constructor
    · exact Fin.insertNth_apply_same (α := fun _ => M) i.succ 1 x
    · funext j
      change i.succ.insertNth (α := fun _ => M) 1 x (i.succAbove j).succ = x j.succ
      rw [← Fin.succ_succAbove_succ, Fin.insertNth_apply_succAbove]
  change i.succ.insertNth (α := fun _ => M) 1 x 0 *
    f (fun j => i.succ.insertNth (α := fun _ => M) 1 x j.succ) =
      x 0 * f (i.insertNth 1 (Fin.tail x))
  rw [h0, ht]

lemma curryMid_rightCoboundary_last {n : ℕ} (f : Cochain M n) :
    (rightCoboundary f).curryMid (Fin.last n) 1 = f := by
  ext x
  change f (fun j => (Fin.last n).insertNth (α := fun _ => M) 1 x j.castSucc) *
    ((Fin.last n).insertNth (α := fun _ => M) 1 x (Fin.last n)) = f x
  simp only [Fin.insertNth_last', Fin.snoc_castSucc, Fin.snoc_last, mul_one]

lemma curryMid_rightCoboundary_castSucc {n : ℕ} (f : Cochain M (n + 1))
    (i : Fin (n + 1)) :
    (rightCoboundary f).curryMid i.castSucc 1 = rightCoboundary (f.curryMid i 1) := by
  ext x
  change f (fun j => i.castSucc.insertNth (α := fun _ => M) 1 x j.castSucc) *
      (i.castSucc.insertNth (α := fun _ => M) 1 x (Fin.last (n + 1))) =
    f (i.insertNth 1 (fun j => x j.castSucc)) * x (Fin.last n)
  rw [init_insert, last_insert]

lemma curryMid_middleCoboundary_castSucc {n : ℕ} (f : Cochain M (n + 1))
    (i : Fin (n + 1)) :
    (middleCoboundary f i).curryMid i.castSucc 1 = f := by
  ext x
  change middleCoboundary f i (i.castSucc.insertNth (α := fun _ => M) 1 x) = f x
  rw [middleCoboundary_apply, merge_insert_same x i 1 (one_mul _)]

lemma merge_insert_succ_one {n : ℕ} (x : Fin (n + 1) → M) (i : Fin (n + 1)) :
    mergeInputs (i.succ.insertNth (α := fun _ => M) 1 x) i = x := by
  ext j
  by_cases hji : j < i
  · simp only [mergeInputs, hji, ite_true]
    rw [tupleInsert_lt _ _ _ _ (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
    rfl
  · by_cases he : j = i
    · subst j
      simp only [mergeInputs, lt_self_iff_false, ite_false, ite_true]
      rw [tupleInsert_lt _ _ _ _ (by simp), Fin.insertNth_apply_same, mul_one]
      rfl
    · have hij : i.val < j.val := by
        have hne : i.val ≠ j.val := fun h => he (Fin.ext h.symm)
        omega
      simp only [mergeInputs, hji, he, ite_false]
      rw [tupleInsert_gt _ _ _ _ (by simpa only [Fin.val_succ, Nat.add_lt_add_iff_right] using hij)]
      rfl

lemma curryMid_middleCoboundary_succ {n : ℕ} (f : Cochain M (n + 1))
    (i : Fin (n + 1)) :
    (middleCoboundary f i).curryMid i.succ 1 = f := by
  ext x
  change middleCoboundary f i (i.succ.insertNth (α := fun _ => M) 1 x) = f x
  rw [middleCoboundary_apply, merge_insert_succ_one]

lemma curryMid_middleCoboundary_after {n : ℕ} (f : Cochain M (n + 2))
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i.val ≤ j.val) :
    (middleCoboundary f j.succ).curryMid i.castSucc 1 =
      middleCoboundary (f.curryMid i 1) j := by
  ext x
  change middleCoboundary f j.succ (i.castSucc.insertNth (α := fun _ => M) 1 x) =
    middleCoboundary (f.curryMid i 1) j x
  simp only [middleCoboundary_apply]
  have hs : i.succAbove j = j.succ :=
    Fin.succAbove_of_le_castSucc i j (by simpa only [Fin.le_def, Fin.val_castSucc] using hij)
  rw [← hs, merge_insert_after x i 1 j hij]
  rfl

lemma merge_insert_succ_before {n : ℕ} (x : Fin (n + 1) → M)
    (i : Fin (n + 1)) (j : Fin n) (hji : j.val < i.val) :
    mergeInputs (i.succ.insertNth (α := fun _ => M) 1 x) j.castSucc =
      i.insertNth 1 (mergeInputs x j) := by
  funext k
  simp only [mergeInputs, ← tupleInsert_eq, tupleInsert, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ, Fin.ext_iff]
  split_ifs <;> try omega
  all_goals first | rfl | congr 1
  all_goals first | rfl | exact Fin.ext (by dsimp; omega)

lemma curryMid_middleCoboundary_before {n : ℕ} (f : Cochain M (n + 2))
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.val < i.val) :
    (middleCoboundary f j.castSucc).curryMid i.succ 1 =
      middleCoboundary (f.curryMid i 1) j := by
  ext x
  change middleCoboundary f j.castSucc (i.succ.insertNth (α := fun _ => M) 1 x) =
    middleCoboundary (f.curryMid i 1) j x
  rw [middleCoboundary_apply, middleCoboundary_apply, merge_insert_succ_before x i j hji]
  rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
