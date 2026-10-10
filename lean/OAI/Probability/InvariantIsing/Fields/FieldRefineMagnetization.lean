import OAI.Probability.InvariantIsing.Fields.FieldRefineIncrements

namespace OAI

/-! Exact magnetization levels under a one-cut field refinement. -/

noncomputable section
open IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldSplitIndex {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) : Fin (n + 1) :=
  if hj : j.val ≤ i.val then ⟨j.val, by omega⟩ else ⟨j.val - 1, by omega⟩

lemma fieldSplitHeight_eq (h : FieldStep) (i : Fin (h.depth + 1))
    (j : Fin (h.depth + 2)) : fieldSplitHeight h i j = h.height (fieldSplitIndex i j) := by
  unfold fieldSplitHeight fieldSplitIndex
  split_ifs <;> rfl

lemma fieldScalarSquareAt_magnetization (h : FieldStep) (i : Fin (h.depth + 1)) :
    fieldScalarSquareAt (fieldAllIncrements h) (fun z => Real.log (Real.cosh z))
      Real.tanh (i.val + 1) 0 = fieldMagnetizationLevel h i := by
  rw [fieldScalarSquareAt_eq (fieldAllIncrements h) _ _
    ⟨i.val + 1, by rw [fieldAllIncrements_length]; omega⟩]
  exact fieldAllSquares_magnetization h i

lemma fieldMagnetizationLevel_insertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 2)) :
    fieldMagnetizationLevel (fieldInsertCut h i c hc₀ hc₁) j =
      fieldMagnetizationLevel h (fieldSplitIndex i j) := by
  apply (fieldScalarSquareAt_magnetization (fieldInsertCut h i c hc₀ hc₁) j).symm.trans
  rw [fieldAllIncrements_insertCut, fieldScalarSquareAt_insert_zero]
  have hp : ((fieldAllIncrements h).take (i.val + 1)).length = i.val + 1 := by
    rw [List.length_take, fieldAllIncrements_length, Nat.min_eq_left (by omega)]
  rw [hp, List.take_append_drop]
  rw [← fieldScalarSquareAt_magnetization]
  by_cases hj : j.val ≤ i.val
  · rw [ite_eq_left (show j.val + 1 ≤ i.val + 1 by omega)]
    simp only [fieldSplitIndex, hj, dite_true]
  · rw [ite_eq_right (show ¬j.val + 1 ≤ i.val + 1 by omega)]
    simp only [fieldSplitIndex, hj, dite_false]
    have hj0 : 0 < j.val := by omega
    congr 2
    omega

end InvariantIsing

end

end OAI
