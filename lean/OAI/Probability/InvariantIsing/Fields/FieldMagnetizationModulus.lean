import OAI.Probability.InvariantIsing.Fields.FieldOverlapIncrement
import OAI.Probability.InvariantIsing.Fields.FieldHeightRegularization

namespace OAI

/-! A uniform modulus for the actual finite-field magnetization levels.
Small height gaps force small overlap gaps, including near tied levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldMagnetizationLevel_increment_le (h : FieldStep) {V : ℝ}
    (hV : h.height (Fin.last h.depth) ≤ V) (i : Fin h.depth) :
    fieldMagnetizationLevel h i.succ - fieldMagnetizationLevel h i.castSucc ≤
      (h.height i.succ - h.height i.castSucc) * fieldGaussianMomentCap (Real.sqrt V) := by
  let L := scalarFieldIncrements h
  let j : Fin L.length := Fin.cast (scalarFieldIncrements_length h).symm i
  have hL := scalarFieldIncrements_positive h
  have hζ : ∀ av ∈ L, av.1 ≤ 1 := by
    intro av hav
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hav
    change h.cut k.succ.castSucc ≤ 1
    rw [← h.last]
    exact h.ordered_cut.monotone (Fin.le_last _)
  have hvar : ∀ av ∈ L, (av.2 : ℝ) ≤ V := by
    intro av hav
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hav
    exact (fieldIncrement_le_last h k.succ).trans hV
  have hb := fieldScalarOverlaps_increment_le L (NNReal.mk (h.height 0) (h.nonneg 0))
    hL hζ hvar j
  have hget : ((L.get j).2 : ℝ) = h.height i.succ - h.height i.castSucc := by
    have hg : L.get j = ((fieldIncrement h i.succ).1,
        NNReal.mk (fieldIncrement h i.succ).2 (fieldIncrement_nonneg h i.succ)) := by
      exact List.get_ofFn (fun k : Fin h.depth => ((fieldIncrement h k.succ).1,
        NNReal.mk (fieldIncrement h k.succ).2 (fieldIncrement_nonneg h k.succ))) j
    rw [hg]
    change (fieldIncrement h i.succ).2 = _
    simp only [fieldIncrement, Fin.val_succ, Nat.succ_ne_zero, dite_false, Nat.add_sub_cancel]
    rfl
  rw [hget] at hb
  change fieldScalarOverlaps L _ _ _ _ - fieldScalarOverlaps L _ _ _ _ ≤ _
  convert hb using 1; congr 1

theorem fieldMagnetizationLevel_sub_le (h : FieldStep) {V : ℝ}
    (hV : h.height (Fin.last h.depth) ≤ V)
    (i j : Fin (h.depth + 1)) (hij : i ≤ j) :
    fieldMagnetizationLevel h j - fieldMagnetizationLevel h i ≤
      (h.height j - h.height i) * fieldGaussianMomentCap (Real.sqrt V) := by
  have hm : Monotone (fun i => h.height i * fieldGaussianMomentCap (Real.sqrt V) -
      fieldMagnetizationLevel h i) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    have hk := fieldMagnetizationLevel_increment_le h hV k
    nlinarith
  have hh := hm hij
  nlinarith

theorem fieldMagnetizationLevel_abs_sub_le (h : FieldStep) {V : ℝ}
    (hV : h.height (Fin.last h.depth) ≤ V) (i j : Fin (h.depth + 1)) :
    |fieldMagnetizationLevel h i - fieldMagnetizationLevel h j| ≤
      |h.height i - h.height j| * fieldGaussianMomentCap (Real.sqrt V) := by
  rcases le_total i j with hij | hji
  · rw [abs_of_nonpos (sub_nonpos.mpr (fieldMagnetizationLevel_monotone h hij)), neg_sub,
      abs_of_nonpos (sub_nonpos.mpr (h.ordered_height hij)), neg_sub]
    exact fieldMagnetizationLevel_sub_le h hV i j hij
  · rw [abs_of_nonneg (sub_nonneg.mpr (fieldMagnetizationLevel_monotone h hji)),
      abs_of_nonneg (sub_nonneg.mpr (h.ordered_height hji))]
    exact fieldMagnetizationLevel_sub_le h hV j i hji

end InvariantIsing

end

end OAI
