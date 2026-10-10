import OAI.Probability.InvariantIsing.Fields.FieldRefineMagnetization
import OAI.Probability.InvariantIsing.Fields.FieldFiniteDomain
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteDeficit

namespace OAI

/-! The height and physical magnetization paths survive a one-cut refinement. -/

noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldInsertCut_cell_subset (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 2)) :
    Ioo ((fieldInsertCut h i c hc₀ hc₁).cut j.castSucc)
        ((fieldInsertCut h i c hc₀ hc₁).cut j.succ) ⊆
      Ioo (h.cut (fieldSplitIndex i j).castSucc) (h.cut (fieldSplitIndex i j).succ) := by
  have hlo : h.cut (fieldSplitIndex i j).castSucc ≤
      (fieldInsertCut h i c hc₀ hc₁).cut j.castSucc := by
    by_cases hj : j.val ≤ i.val
    · rw [fieldInsertCut_cut_below h i c hc₀ hc₁ j.castSucc hj]
      simp only [fieldSplitIndex, hj, dite_true]
      rfl
    · by_cases he : j.val = i.val + 1
      · have hjc : j.castSucc = i.castSucc.succ := Fin.ext he
        rw [hjc, fieldInsertCut_cut_at]
        convert hc₀.le using 1
        congr 1
        apply Fin.ext
        simp only [fieldSplitIndex, hj, dite_false, Fin.val_castSucc]
        omega
      · rw [fieldInsertCut_cut_above h i c hc₀ hc₁ j.castSucc (by
          change i.val + 1 < j.val; omega)]
        simp only [fieldSplitIndex, hj, dite_false]
        rfl
  have hhi : (fieldInsertCut h i c hc₀ hc₁).cut j.succ ≤
      h.cut (fieldSplitIndex i j).succ := by
    by_cases hj : j.val < i.val
    · rw [fieldInsertCut_cut_below h i c hc₀ hc₁ j.succ (by
        change j.val + 1 ≤ i.val; omega)]
      simp only [fieldSplitIndex, show j.val ≤ i.val from hj.le, dite_true]
      rfl
    · by_cases he : j.val = i.val
      · have hjc : j.succ = i.castSucc.succ := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        rw [hjc, fieldInsertCut_cut_at]
        convert hc₁.le using 1
        congr 1
        apply Fin.ext
        simp only [fieldSplitIndex, show j.val ≤ i.val by omega, dite_true, Fin.val_succ]
        omega
      · have hgt : i.val < j.val := by omega
        rw [fieldInsertCut_cut_above h i c hc₀ hc₁ j.succ (by
          change i.val + 1 < j.val + 1; omega)]
        simp only [fieldSplitIndex, show ¬j.val ≤ i.val by omega, dite_false,
          Fin.val_succ, Nat.add_sub_cancel]
        apply le_of_eq
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
  intro s hs
  exact ⟨hlo.trans_lt hs.1, hs.2.trans_le hhi⟩

lemma fieldFunction_insertCut_ae (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    fieldFunction (fieldInsertCut h i c hc₀ hc₁) =ᵐ[pathMeasure] fieldFunction h := by
  filter_upwards [ae_finite_overlap_cell (fieldInsertCut h i c hc₀ hc₁).cut
    (fieldInsertCut h i c hc₀ hc₁).first (fieldInsertCut h i c hc₀ hc₁).last] with s hs
  obtain ⟨j, hj⟩ := hs
  have hi := fieldInsertCut_cell_subset h i c hc₀ hc₁ j hj
  change finiteStepFunction _ _ s = finiteStepFunction _ _ s
  rw [finiteStepFunction_on_cell (fieldInsertCut h i c hc₀ hc₁).ordered_cut _ hj,
    finiteStepFunction_on_cell h.ordered_cut _ hi]
  exact fieldSplitHeight_eq h i j

lemma fieldMagnetizationPath_insertCut_ae (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    (fieldMagnetizationPath (fieldInsertCut h i c hc₀ hc₁)).val =ᵐ[pathMeasure]
      (fieldMagnetizationPath h).val := by
  filter_upwards [ae_finite_overlap_cell (fieldInsertCut h i c hc₀ hc₁).cut
    (fieldInsertCut h i c hc₀ hc₁).first (fieldInsertCut h i c hc₀ hc₁).last] with s hs
  obtain ⟨j, hj⟩ := hs
  have hi := fieldInsertCut_cell_subset h i c hc₀ hc₁ j hj
  rw [fieldMagnetizationPath_on_cell _ j hj,
    fieldMagnetizationPath_on_cell h (fieldSplitIndex i j) hi]
  exact fieldMagnetizationLevel_insertCut h i c hc₀ hc₁ j

end InvariantIsing

end

end OAI
