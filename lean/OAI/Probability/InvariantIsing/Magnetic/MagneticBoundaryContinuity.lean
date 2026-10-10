import OAI.Probability.InvariantIsing.Fields.FieldHeightBoundaryContinuity
import OAI.Probability.InvariantIsing.Magnetic.MagneticImplicitBias
import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldLevels

namespace OAI

/-! Continuity of the prescribed-magnetization functional along the strict
height regularization, including coincident heights and zero root variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped NNReal Topology

namespace InvariantIsing

lemma fieldRegularized_depth (h : FieldStep) (t : ℝ) :
    (fieldRegularized h t).depth = h.depth := rfl

lemma continuous_fieldRegularizedValue_bias (h : FieldStep) :
    Continuous (fun p : ℝ × ℝ => fieldValue (fieldRegularized h p.1) p.2) := by
  let L := fieldRegularizedIncrements h
  let V := h.height (Fin.last h.depth) + 1
  have hV : 0 ≤ V := add_nonneg (h.nonneg _) zero_le_one
  have hL := fieldRegularizedIncrements_positive h
  have hc := fieldRegularizedIncrements_continuous h
  have hv := fieldRegularizedIncrements_bound h
  have hval := continuous_fieldVaryingValue L hL hc hV hv
  obtain ⟨hcap, hb⟩ := fieldVaryingValue_bound L hL hV hv
  have hroot : Continuous (fun p : ℝ × ℝ => (fieldRegularizedRoot h p.1 : ℝ)) :=
    (NNReal.continuous_coe.comp (continuous_fieldRegularizedRoot h)).comp continuous_fst
  have hi := continuous_field_gaussian_integral (E := ℝ × ℝ)
    (U := fun p y => fieldVaryingValue L p.1 y)
    (hval.comp (continuous_fst.fst.prodMk continuous_snd)) hroot continuous_snd
    hcap zero_le_one (fun p y => by simpa only [one_mul] using hb p.1 y)
  have hlast : Continuous (fun p : ℝ × ℝ =>
      (fieldRegularized h p.1).height (Fin.last h.depth) / 2) := by
    change Continuous (fun p : ℝ × ℝ => (h.height (Fin.last h.depth) +
      fieldHeightEpsilon p.1 * ((Fin.last h.depth).val + 1 : ℕ)) / 2)
    have heps := continuous_fieldHeightEpsilon
    fun_prop
  convert hi.sub hlast using 1
  funext p
  rw [fieldValue_root, ← fieldRegularizedIncrements_eval,
    ← fieldVaryingValue_eq_scalar]
  simp only [gaussianOperator, ite_true, fieldRegularized, fieldWithHeights,
    fieldRegularizedHeight, Fin.val_zero, zero_add, Nat.cast_one, mul_one,
    fieldRegularizedRoot, NNReal.coe_mk, Pi.sub_apply, L]
  rfl

lemma continuous_fieldRegularizedMean_bias (h : FieldStep) :
    Continuous (fun p : ℝ × ℝ => fieldBiasMean (fieldRegularized h p.1) p.2) := by
  let L := fieldRegularizedIncrements h
  let V := h.height (Fin.last h.depth) + 1
  have hV : 0 ≤ V := add_nonneg (h.nonneg _) zero_le_one
  have hL := fieldRegularizedIncrements_positive h
  have hc := fieldRegularizedIncrements_continuous h
  have hv := fieldRegularizedIncrements_bound h
  have hm := continuous_fieldVaryingMean L hL hc hV hv
  have hroot : Continuous (fun p : ℝ × ℝ => (fieldRegularizedRoot h p.1 : ℝ)) :=
    (NNReal.continuous_coe.comp (continuous_fieldRegularizedRoot h)).comp continuous_fst
  have hi := continuous_field_gaussian_integral (E := ℝ × ℝ)
    (U := fun p y => fieldVaryingMean L p.1 y)
    (hm.comp (continuous_fst.fst.prodMk continuous_snd)) hroot continuous_snd
    zero_le_one (le_refl (0 : ℝ)) (fun p y => by
      simpa only [zero_mul, add_zero] using (fieldVaryingMean_regular L hL p.1).2 y)
  convert hi using 1
  funext p
  unfold fieldBiasMean
  rw [← fieldRegularizedIncrements_eval, ← fieldVaryingValue_eq_scalar,
    ← fieldVaryingMean_eq_scalar,
    fieldSpinTransition_eq_standard 0 _ (fieldVaryingValue_regular L hL p.1).1
      (fieldVaryingMean_regular L hL p.1).1, gaussianTiltAverage_zero]
  simp only [fieldRegularizedRoot, fieldRegularized, fieldWithHeights,
    fieldRegularizedHeight, Fin.val_zero, zero_add, Nat.cast_one, mul_one, NNReal.coe_mk]
  rfl

lemma continuous_fieldRegularizedLevel_bias (h : FieldStep) (i : Fin (h.depth + 1)) :
    Continuous (fun p : ℝ × ℝ => magneticLevelAtBias (fieldRegularized h p.1) p.2 i) := by
  let L := fieldRegularizedIncrements h
  let V := h.height (Fin.last h.depth) + 1
  have hV : 0 ≤ V := add_nonneg (h.nonneg _) zero_le_one
  have hL := fieldRegularizedIncrements_positive h
  have hc := fieldRegularizedIncrements_continuous h
  have hv := fieldRegularizedIncrements_bound h
  let j : Fin (L.length + 1) := ⟨i.val, by
    simpa only [L, fieldRegularizedIncrements, List.length_ofFn] using i.isLt⟩
  have hm := continuous_fieldVaryingSquares L hL hc hV hv j
  have hroot : Continuous (fun p : ℝ × ℝ => (fieldRegularizedRoot h p.1 : ℝ)) :=
    (NNReal.continuous_coe.comp (continuous_fieldRegularizedRoot h)).comp continuous_fst
  have hi := continuous_field_gaussian_integral (E := ℝ × ℝ)
    (U := fun p y => fieldVaryingSquares L p.1 j y)
    (hm.comp (continuous_fst.fst.prodMk continuous_snd)) hroot continuous_snd
    zero_le_one (le_refl (0 : ℝ)) (fun p y => by
      have hb := (fieldVaryingSquares_regular L hL p.1 j).2 y
      simpa only [zero_mul, add_zero, abs_of_nonneg hb.1] using hb.2)
  convert hi using 1
  funext p
  change fieldSpinTransition 0 (NNReal.mk ((fieldRegularized h p.1).height 0)
    ((fieldRegularized h p.1).nonneg 0))
    (fieldScalarValue (scalarFieldIncrements (fieldRegularized h p.1))
      (fun z => Real.log (Real.cosh z)))
    (fieldScalarSquares (scalarFieldIncrements (fieldRegularized h p.1))
      (fun z => Real.log (Real.cosh z)) Real.tanh
      ⟨i.val, by rw [scalarFieldIncrements_length, fieldRegularized_depth]; exact i.isLt⟩) p.2 = _
  have he : fieldScalarSquares (scalarFieldIncrements (fieldRegularized h p.1))
      (fun z => Real.log (Real.cosh z)) Real.tanh
      ⟨i.val, by rw [scalarFieldIncrements_length, fieldRegularized_depth]; exact i.isLt⟩ =
      fieldVaryingSquares L p.1 j := by
    rw [fieldVaryingSquares_eq_scalar]
    exact fieldScalarSquares_congr_list (fieldRegularizedIncrements_eval h p.1).symm
      (fun z => Real.log (Real.cosh z)) Real.tanh _ _ rfl
  rw [he, ← fieldRegularizedIncrements_eval, ← fieldVaryingValue_eq_scalar,
    fieldSpinTransition_eq_standard 0 _ (fieldVaryingValue_regular L hL p.1).1
      (fieldVaryingSquares_regular L hL p.1 j).1, gaussianTiltAverage_zero]
  simp only [fieldRegularizedRoot, fieldRegularized, fieldWithHeights,
    fieldRegularizedHeight, Fin.val_zero, zero_add, Nat.cast_one, mul_one, NNReal.coe_mk]
  rfl

lemma continuous_fieldRegularizedMagneticBias (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    Continuous (fun t => magneticBias (fieldRegularized h t) s) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply parametric_bias_continuousAt
    (A := fun p => fieldBiasMean (fieldRegularized h p.1) p.2)
    (s := s)
  · intro z
    exact ((continuous_fieldRegularizedMean_bias h).comp
      (continuous_id.prodMk continuous_const)).continuousAt
  · exact Eventually.of_forall (fun q => strictMono_fieldBiasMean (fieldRegularized h q))
  · exact Eventually.of_forall (fun q => fieldBiasMean_magneticBias (fieldRegularized h q) hs)

lemma continuous_fieldRegularizedConstrainedValue (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    Continuous (fun t => constrainedFieldValue (fieldRegularized h t) s) := by
  have hb := continuous_fieldRegularizedMagneticBias h hs
  have hv := (continuous_fieldRegularizedValue_bias h).comp (continuous_id.prodMk hb)
  convert hv.sub (hb.mul_const s) using 1
  funext t
  exact constrainedFieldValue_magneticBias (fieldRegularized h t) hs

lemma continuous_fieldRegularizedMagneticLevel (h : FieldStep) {s : ℝ} (hs : |s| < 1)
    (i : Fin (h.depth + 1)) :
    Continuous (fun t => magneticFieldLevel (fieldRegularized h t) s i) := by
  have hb : Continuous (fun t => magneticBias (fieldRegularized h t) s) :=
    continuous_fieldRegularizedMagneticBias h hs
  have hp : Continuous (fun t : ℝ => (t, magneticBias (fieldRegularized h t) s)) :=
    continuous_id.prodMk hb
  have hc : Continuous (fun p : ℝ × ℝ =>
      magneticLevelAtBias (fieldRegularized h p.1) p.2 i) :=
    continuous_fieldRegularizedLevel_bias h i
  change Continuous (fun t : ℝ => magneticLevelAtBias (fieldRegularized h t)
    (magneticBias (fieldRegularized h t) s) i)
  simpa only [Function.comp_def] using hc.comp hp

end InvariantIsing

end

end OAI
