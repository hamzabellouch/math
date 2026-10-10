import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldLevels
import OAI.Probability.InvariantIsing.Fields.FieldCommonRefinement

namespace OAI

/-! Prescribed-magnetization values and conditional spin products are
unchanged by subdivision of a tied covariance interval. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma FieldRefines.biasMean {h k : FieldStep} (hk : FieldRefines h k) :
    fieldBiasMean k = fieldBiasMean h := by
  funext b
  have hd := hasDerivAt_fieldValue_bias k b
  have he : fieldValue k = fieldValue h := funext hk.value
  rw [he] at hd
  exact hd.unique (hasDerivAt_fieldValue_bias h b)

lemma FieldRefines.magneticBias {h k : FieldStep} (hk : FieldRefines h k) :
    magneticBias k = magneticBias h :=
  congrArg Function.invFun hk.biasMean

lemma FieldRefines.constrainedValue {h k : FieldStep} (hk : FieldRefines h k) (s : ℝ) :
    constrainedFieldValue k s = constrainedFieldValue h s := by
  unfold constrainedFieldValue magneticBiasObjective
  simp only [hk.value]

lemma fieldScalarSquareAt_magneticLevel (h : FieldStep) (b : ℝ)
    (i : Fin (h.depth + 1)) :
    fieldScalarSquareAt (fieldAllIncrements h) (fun z => Real.log (Real.cosh z))
      Real.tanh (i.val + 1) b = magneticLevelAtBias h b i := by
  rw [fieldScalarSquareAt_eq (fieldAllIncrements h) _ _
    ⟨i.val + 1, by rw [fieldAllIncrements_length]; omega⟩]
  exact (magneticLevelAtBias_allSquares h b i).symm

lemma magneticLevelAtBias_insertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) (b : ℝ)
    (j : Fin (h.depth + 2)) :
    magneticLevelAtBias (fieldInsertCut h i c hc₀ hc₁) b j =
      magneticLevelAtBias h b (fieldSplitIndex i j) := by
  apply (fieldScalarSquareAt_magneticLevel (fieldInsertCut h i c hc₀ hc₁) b j).symm.trans
  rw [fieldAllIncrements_insertCut, fieldScalarSquareAt_insert_zero]
  have hp : ((fieldAllIncrements h).take (i.val + 1)).length = i.val + 1 := by
    rw [List.length_take, fieldAllIncrements_length, Nat.min_eq_left (by omega)]
  rw [hp, List.take_append_drop]
  rw [← fieldScalarSquareAt_magneticLevel]
  by_cases hj : j.val ≤ i.val
  · rw [ite_eq_left (show j.val + 1 ≤ i.val + 1 by omega)]
    simp only [fieldSplitIndex, hj, dite_true]
  · rw [ite_eq_right (show ¬j.val + 1 ≤ i.val + 1 by omega)]
    simp only [fieldSplitIndex, hj, dite_false]
    have hj0 : 0 < j.val := by omega
    congr 2
    omega

lemma magneticFieldLevel_insertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) (s : ℝ)
    (j : Fin (h.depth + 2)) :
    magneticFieldLevel (fieldInsertCut h i c hc₀ hc₁) s j =
      magneticFieldLevel h s (fieldSplitIndex i j) := by
  have hr : FieldRefines h (fieldInsertCut h i c hc₀ hc₁) :=
    FieldRefines.insert (FieldRefines.refl h) i c hc₀ hc₁
  unfold magneticFieldLevel
  rw [hr.magneticBias, magneticLevelAtBias_insertCut]

lemma magneticFieldPath_on_cell (h : FieldStep) (s : ℝ) (i : Fin (h.depth + 1))
    {t : ℝ} (ht : t ∈ Set.Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    magneticFieldPath h s t = magneticFieldLevel h s i :=
  fieldLevelPath_on_cell h _ _ _ i ht

lemma magneticFieldPath_insertCut_ae (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) (s : ℝ) :
    (magneticFieldPath (fieldInsertCut h i c hc₀ hc₁) s).val =ᵐ[pathMeasure]
      (magneticFieldPath h s).val := by
  filter_upwards [ae_finite_overlap_cell (fieldInsertCut h i c hc₀ hc₁).cut
    (fieldInsertCut h i c hc₀ hc₁).first (fieldInsertCut h i c hc₀ hc₁).last] with t ht
  obtain ⟨j, hj⟩ := ht
  have hi := fieldInsertCut_cell_subset h i c hc₀ hc₁ j hj
  rw [magneticFieldPath_on_cell _ s j hj,
    magneticFieldPath_on_cell h s (fieldSplitIndex i j) hi]
  exact magneticFieldLevel_insertCut h i c hc₀ hc₁ s j

lemma FieldRefines.magneticPath_ae {h k : FieldStep} (hk : FieldRefines h k) (s : ℝ) :
    (magneticFieldPath k s).val =ᵐ[pathMeasure] (magneticFieldPath h s).val := by
  induction hk with
  | refl => exact Filter.EventuallyEq.rfl
  | insert hk i c hc₀ hc₁ ih =>
    exact (magneticFieldPath_insertCut_ae _ i c hc₀ hc₁ s).trans ih

end InvariantIsing

end

end OAI
