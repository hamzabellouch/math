import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldSymmetry
import OAI.Probability.InvariantIsing.Fields.FieldHeightChart

namespace OAI

/-! The actual conditional squared spin means at prescribed magnetization.
The root Gaussian is averaged at the optimizing bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

private lemma field_measurable_tanh : Measurable Real.tanh := by
  change Measurable (fun x : ℝ => Real.tanh x)
  simp only [Real.tanh_eq]
  fun_prop

def magneticLevelAtBias (h : FieldStep) (b : ℝ) (i : Fin (h.depth + 1)) : ℝ :=
  fieldSpinTransition 0 (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)))
    (fieldScalarSquares (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)) Real.tanh
      (Fin.cast (by rw [scalarFieldIncrements_length]) i)) b

lemma magneticLevelAtBias_allSquares (h : FieldStep) (b : ℝ)
    (i : Fin (h.depth + 1)) :
    magneticLevelAtBias h b i =
      fieldScalarSquares (fieldAllIncrements h) (fun z => Real.log (Real.cosh z)) Real.tanh
        ⟨i.val + 1, by simp only [fieldAllIncrements_length]; omega⟩ b := by
  let j : Fin ((scalarFieldIncrements h).length + 1) :=
    Fin.cast (by rw [scalarFieldIncrements_length]) i
  have he := fieldScalarSquares_congr_list (fieldAllIncrements_root h) (fun z => Real.log (Real.cosh z)) Real.tanh
    ⟨i.val + 1, by simp only [fieldAllIncrements_length]; omega⟩ j.succ (by rfl)
  rw [congrFun he b]
  rfl

lemma magneticLevelAtBias_zero (h : FieldStep) (i : Fin (h.depth + 1)) :
    magneticLevelAtBias h 0 i = fieldMagnetizationLevel h i := by
  rw [magneticLevelAtBias_allSquares]
  exact fieldAllSquares_magnetization h i

lemma magneticLevelAtBias_mem_unit (h : FieldStep) (b : ℝ)
    (i : Fin (h.depth + 1)) : magneticLevelAtBias h b i ∈ Icc (0 : ℝ) 1 := by
  have hL := scalarFieldIncrements_positive h
  have hR := fieldScalarSquares_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth field_measurable_tanh field_abs_tanh_le_one
    (Fin.cast (by rw [scalarFieldIncrements_length]) i)
  have hv := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hb := fieldSpinTransition_bound 0 (NNReal.mk (h.height 0) (h.nonneg 0))
    hv.1 hv.2 (fun z => by rw [abs_of_nonneg (hR.2 z).1]; exact (hR.2 z).2) b
  refine ⟨?_, (le_abs_self _).trans hb⟩
  unfold magneticLevelAtBias fieldSpinTransition
  exact integral_nonneg (fun z => (hR.2 z).1)

lemma magneticLevelAtBias_monotone (h : FieldStep) (b : ℝ) :
    Monotone (magneticLevelAtBias h b) := by
  have hL := scalarFieldIncrements_positive h
  have hR := fieldScalarSquares_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth field_measurable_tanh field_abs_tanh_le_one
  intro i j hij
  apply fieldSpinTransition_mono_test
    0 (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)))
    (hR _).1 (hR _).1
    (fun z => by rw [abs_of_nonneg ((hR _).2 z).1]; exact ((hR _).2 z).2)
    (fun z => by rw [abs_of_nonneg ((hR _).2 z).1]; exact ((hR _).2 z).2)
  intro z
  exact fieldScalarSquares_monotone (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth field_measurable_tanh field_abs_tanh_le_one z hij

lemma fieldBiasMean_sq_le_magneticLevel (h : FieldStep) (b : ℝ)
    (i : Fin (h.depth + 1)) : (fieldBiasMean h b) ^ 2 ≤ magneticLevelAtBias h b i := by
  have hL := scalarFieldIncrements_positive h
  have hv := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hm := fieldScalarMean_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth field_measurable_tanh field_abs_tanh_le_one
  have hsq := fieldSpinTransition_square_le 0 (NNReal.mk (h.height 0) (h.nonneg 0))
    hv.1 hv.2 hm.1 hm.2 b
  have he : magneticLevelAtBias h b 0 =
      fieldSpinTransition 0 (NNReal.mk (h.height 0) (h.nonneg 0))
        (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)))
        (fun z => (fieldScalarMean (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)) Real.tanh z) ^ 2) b := by
    unfold magneticLevelAtBias
    congr 1
    funext z
    exact fieldScalarSquares_zero _ _ _ z
  change (fieldBiasMean h b) ^ 2 ≤ _ at hsq
  rw [← he] at hsq
  exact hsq.trans (magneticLevelAtBias_monotone h b (Fin.zero_le i))

def magneticFieldLevel (h : FieldStep) (s : ℝ) : Fin (h.depth + 1) → ℝ :=
  magneticLevelAtBias h (magneticBias h s)

lemma magneticFieldLevel_mem_unit (h : FieldStep) (s : ℝ)
    (i : Fin (h.depth + 1)) : magneticFieldLevel h s i ∈ Icc (0 : ℝ) 1 :=
  magneticLevelAtBias_mem_unit h _ i

lemma magneticFieldLevel_monotone (h : FieldStep) (s : ℝ) :
    Monotone (magneticFieldLevel h s) := magneticLevelAtBias_monotone h _

lemma sq_magnetization_le_magneticFieldLevel (h : FieldStep) {s : ℝ}
    (hs : |s| < 1) (i : Fin (h.depth + 1)) : s ^ 2 ≤ magneticFieldLevel h s i := by
  have hh := fieldBiasMean_sq_le_magneticLevel h (magneticBias h s) i
  rwa [fieldBiasMean_magneticBias h hs] at hh

def magneticFieldPath (h : FieldStep) (s : ℝ) : OverlapPath :=
  fieldLevelPath h (magneticFieldLevel h s) (magneticFieldLevel_monotone h s)
    (magneticFieldLevel_mem_unit h s)

@[simp] lemma magneticFieldLevel_zero (h : FieldStep) (i : Fin (h.depth + 1)) :
    magneticFieldLevel h 0 i = fieldMagnetizationLevel h i := by
  simp only [magneticFieldLevel, magneticBias_zero, magneticLevelAtBias_zero]

end InvariantIsing

end

end OAI
