import OAI.Probability.InvariantIsing.Fields.FieldRefineCut

namespace OAI

/-! A one-cut refinement inserts exactly one zero covariance increment. -/

noncomputable section
open IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldIncrement_insertCut_at (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    fieldIncrement (fieldInsertCut h i c hc₀ hc₁) i.succ = (c, 0) := by
  apply Prod.ext
  · change (fieldInsertCut h i c hc₀ hc₁).cut i.succ.castSucc = c
    simpa only [Fin.succ_castSucc] using fieldInsertCut_cut_at h i c hc₀ hc₁
  · change fieldSplitHeight h i i.succ -
      (if hz : i.succ.val = 0 then 0 else
        fieldSplitHeight h i ⟨i.succ.val - 1, by change i.val + 1 - 1 < h.depth + 2; omega⟩) = 0
    simp only [Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      dite_false, Nat.add_sub_cancel]
    unfold fieldSplitHeight
    simp only [Fin.val_succ]
    rw [dite_eq_right (show ¬i.val + 1 ≤ i.val by omega),
      dite_eq_left (show i.val ≤ i.val by omega)]
    simp

lemma fieldIncrement_insertCut_below (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 1)) (hj : j.val ≤ i.val) :
    fieldIncrement (fieldInsertCut h i c hc₀ hc₁) j.castSucc = fieldIncrement h j := by
  apply Prod.ext
  · exact fieldInsertCut_cut_below h i c hc₀ hc₁ _ hj
  · change fieldSplitHeight h i j.castSucc -
      (if hz : j.val = 0 then 0 else fieldSplitHeight h i ⟨j.val - 1, by omega⟩) =
        h.height j - (if hz : j.val = 0 then 0 else h.height ⟨j.val - 1, by omega⟩)
    have hp : fieldSplitHeight h i j.castSucc = h.height j := by
      unfold fieldSplitHeight
      exact dite_eq_left hj
    rw [hp]
    split_ifs with hz
    · rfl
    · have hp' : fieldSplitHeight h i ⟨j.val - 1, by omega⟩ =
          h.height ⟨j.val - 1, by omega⟩ := by
        unfold fieldSplitHeight
        exact dite_eq_left (show j.val - 1 ≤ i.val by omega)
      rw [hp']

lemma fieldIncrement_insertCut_above (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 1)) (hj : i.val < j.val) :
    fieldIncrement (fieldInsertCut h i c hc₀ hc₁) j.succ = fieldIncrement h j := by
  apply Prod.ext
  · change (fieldInsertCut h i c hc₀ hc₁).cut j.succ.castSucc = h.cut j.castSucc
    convert fieldInsertCut_cut_above h i c hc₀ hc₁ j.succ.castSucc (by
      change i.val + 1 < j.val + 1; omega) using 1
    congr 1
  · change fieldSplitHeight h i j.succ -
      (if hz : j.val + 1 = 0 then 0 else fieldSplitHeight h i ⟨j.val + 1 - 1, by omega⟩) =
        h.height j - (if hz : j.val = 0 then 0 else h.height ⟨j.val - 1, by omega⟩)
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]
    have hp : fieldSplitHeight h i j.succ = h.height j := by
      unfold fieldSplitHeight
      rw [dite_eq_right (show ¬j.succ.val ≤ i.val by change ¬j.val + 1 ≤ i.val; omega)]
      rfl
    have hp' : fieldSplitHeight h i ⟨j.val + 1 - 1, by omega⟩ =
        h.height ⟨j.val - 1, by omega⟩ := by
      unfold fieldSplitHeight
      rw [dite_eq_right (by change ¬j.val + 1 - 1 ≤ i.val; omega)]
      rfl
    rw [hp, hp']

def fieldNNIncrement (h : FieldStep) (i : Fin (h.depth + 1)) : ℝ × ℝ≥0 :=
  ((fieldIncrement h i).1, NNReal.mk (fieldIncrement h i).2 (fieldIncrement_nonneg h i))

lemma fieldNNIncrement_eq_of_real {h k : FieldStep} {i : Fin (h.depth + 1)}
    {j : Fin (k.depth + 1)} (he : fieldIncrement h i = fieldIncrement k j) :
    fieldNNIncrement h i = fieldNNIncrement k j := by
  apply Prod.ext
  · exact congrArg (fun p : ℝ × ℝ => p.1) he
  · apply Subtype.ext
    exact congrArg (fun p : ℝ × ℝ => p.2) he

lemma fieldNNIncrement_insertCut_at (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    fieldNNIncrement (fieldInsertCut h i c hc₀ hc₁) i.succ = (c, 0) := by
  have he := fieldIncrement_insertCut_at h i c hc₀ hc₁
  apply Prod.ext
  · change (fieldIncrement (fieldInsertCut h i c hc₀ hc₁) i.succ).1 = c
    exact congrArg (fun p : ℝ × ℝ => p.1) he
  · apply Subtype.ext
    change (fieldIncrement (fieldInsertCut h i c hc₀ hc₁) i.succ).2 = 0
    exact congrArg (fun p : ℝ × ℝ => p.2) he

lemma fieldAllIncrements_insertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    fieldAllIncrements (fieldInsertCut h i c hc₀ hc₁) =
      (fieldAllIncrements h).take (i.val + 1) ++
        (c, 0) :: (fieldAllIncrements h).drop (i.val + 1) := by
  let f : Fin (h.depth + 1) → ℝ × ℝ≥0 := fieldNNIncrement h
  let g : Fin (h.depth + 2) → ℝ × ℝ≥0 :=
    fieldNNIncrement (fieldInsertCut h i c hc₀ hc₁)
  have he : g = Fin.insertNth i.succ (c, 0) f := by
    apply (Fin.eq_insertNth_iff).mpr
    constructor
    · exact fieldNNIncrement_insertCut_at h i c hc₀ hc₁
    · funext j
      change g (i.succ.succAbove j) = f j
      by_cases hj : j.val ≤ i.val
      · have hs : i.succ.succAbove j = j.castSucc :=
          Fin.succAbove_of_castSucc_lt _ _ (by change j.val < i.val + 1; omega)
        rw [hs]
        exact fieldNNIncrement_eq_of_real (fieldIncrement_insertCut_below h i c hc₀ hc₁ j hj)
      · have hs : i.succ.succAbove j = j.succ :=
          Fin.succAbove_of_le_castSucc _ _ (by change i.val + 1 ≤ j.val; omega)
        rw [hs]
        exact fieldNNIncrement_eq_of_real (fieldIncrement_insertCut_above h i c hc₀ hc₁ j (by omega))
  change List.ofFn g = (List.ofFn f).take (i.val + 1) ++ (c, 0) :: (List.ofFn f).drop (i.val + 1)
  rw [he, field_ofFn_insertNth]
  rfl

lemma fieldValue_insertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) (z : ℝ) :
    fieldValue (fieldInsertCut h i c hc₀ hc₁) z = fieldValue h z := by
  rw [← fieldAllIncrements_value, fieldAllIncrements_insertCut,
    fieldScalarValue_insert_zero, List.take_append_drop]
  change fieldScalarValue (fieldAllIncrements h) (fun y => Real.log (Real.cosh y)) z -
    (fieldInsertCut h i c hc₀ hc₁).height (Fin.last (h.depth + 1)) / 2 = _
  rw [fieldInsertCut_last_height, fieldAllIncrements_value]

end InvariantIsing

end

end OAI
