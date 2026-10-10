import OAI.Probability.InvariantIsing.Magnetic.MagneticInverseCurvature
import OAI.Probability.InvariantIsing.Fields.FieldSpinLinear

namespace OAI

/-! The physical curvature is bounded by the remaining spin variance.
Consequently its mean-coordinate representative vanishes at both endpoints. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldCurvatureTransform_le_spin_variance {ζ : ℝ} (hζ : ζ ≤ 1) (v : ℝ≥0)
    {F M Q : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q)
    {K C : ℝ} (bM : ∀ y, |M y| ≤ K) (bQ : ∀ y, |Q y| ≤ C)
    (hbound : ∀ y, Q y + (M y) ^ 2 ≤ 1) (z : ℝ) :
    fieldCurvatureTransform ζ v F M Q z ≤ 1 - (fieldSpinTransition ζ v F M z) ^ 2 := by
  have bM2 : ∀ y, |(M y) ^ 2| ≤ K ^ 2 := by
    intro y
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (bM y) 2
  have hle := fieldSpinTransition_mono_test ζ v F (hQ.add (hM.pow_const 2))
    measurable_const
    (fun y => (abs_add_le _ _).trans (add_le_add (bQ y) (bM2 y)))
    (fun _ => by norm_num : ∀ y : ℝ, |(1 : ℝ)| ≤ 1) hbound z
  change fieldSpinTransition ζ v F (fun y => Q y + M y ^ 2) z ≤
    fieldSpinTransition ζ v F (fun _ => 1) z at hle
  rw [fieldSpinTransition_add ζ v hF hG hQ (hM.pow_const 2) bQ bM2,
    fieldSpinTransition_const ζ v hF hG] at hle
  have hvar := fieldSpinTransition_square_le ζ v hF hG hM bM z
  have hc : ζ * (fieldSpinTransition ζ v F (fun y => M y ^ 2) z -
      (fieldSpinTransition ζ v F M z) ^ 2) ≤
      fieldSpinTransition ζ v F (fun y => M y ^ 2) z -
      (fieldSpinTransition ζ v F M z) ^ 2 := by
    exact mul_le_of_le_one_left (sub_nonneg.mpr hvar) hζ
  unfold fieldCurvatureTransform
  linarith

lemma field_logCosh_spin_variance (z : ℝ) :
    1 / (Real.cosh z) ^ 2 + (Real.tanh z) ^ 2 = 1 := by
  have hc := (Real.cosh_pos z).ne'
  have hr := Real.cosh_sq_sub_sinh_sq z
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hc]
  nlinarith

lemma fieldScalarLogCoshSecond_le_spin_variance (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hζ : ∀ av ∈ L, av.1 ≤ 1) (z : ℝ) :
    fieldScalarSecond L (fun y => Real.log (Real.cosh y)) Real.tanh
      (fun y => 1 / (Real.cosh y) ^ 2) z ≤
      1 - (fieldScalarMean L (fun y => Real.log (Real.cosh y)) Real.tanh z) ^ 2 := by
  induction L generalizing z with
  | nil =>
    change 1 / (Real.cosh z) ^ 2 ≤ 1 - (Real.tanh z) ^ 2
    linarith [field_logCosh_spin_variance z]
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have htζ := fun bv hb => hζ bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hm : Measurable Real.tanh := by
      change Measurable (fun x : ℝ => Real.tanh x)
      simp only [Real.tanh_eq]
      fun_prop
    have ha := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      hm field_abs_tanh_le_one
    have hq := fieldScalarLogCoshSecond_regular L ht
    have hb : ∀ y, fieldScalarSecond L (fun y => Real.log (Real.cosh y)) Real.tanh
        (fun y => 1 / (Real.cosh y) ^ 2) y +
        (fieldScalarMean L (fun y => Real.log (Real.cosh y)) Real.tanh y) ^ 2 ≤ 1 := by
      intro y
      linarith [ih ht htζ y]
    exact fieldCurvatureTransform_le_spin_variance (hζ av List.mem_cons_self) av.2
      hv.1 hv.2 ha.1 hq.1 ha.2 hq.2 hb z

lemma fieldBiasCurvature_le_spin_variance (h : FieldStep) (b : ℝ) :
    fieldBiasCurvature h b ≤ 1 - (fieldBiasMean h b) ^ 2 := by
  have hL := scalarFieldIncrements_positive h
  have hζ : ∀ av ∈ scalarFieldIncrements h, av.1 ≤ 1 := by
    intro av hav
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
    change h.cut i.succ.castSucc ≤ 1
    rw [← h.last]
    exact h.ordered_cut.monotone (Fin.le_last _)
  have hv := fieldScalarValue_regular _ hL measurable_logCosh logCosh_linearGrowth
  have hm : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have ha := fieldScalarMean_regular _ hL measurable_logCosh logCosh_linearGrowth
    hm field_abs_tanh_le_one
  have hq := fieldScalarLogCoshSecond_regular _ hL
  have hb : ∀ y, fieldScalarSecond (scalarFieldIncrements h)
      (fun y => Real.log (Real.cosh y)) Real.tanh (fun y => 1 / (Real.cosh y) ^ 2) y +
      (fieldScalarMean (scalarFieldIncrements h) (fun y => Real.log (Real.cosh y)) Real.tanh y) ^ 2 ≤ 1 := by
    intro y
    linarith [fieldScalarLogCoshSecond_le_spin_variance _ hL hζ y]
  have hh := fieldCurvatureTransform_le_spin_variance (by norm_num : (0 : ℝ) ≤ 1)
    (NNReal.mk (h.height 0) (h.nonneg 0)) hv.1 hv.2 ha.1 hq.1 ha.2 hq.2 hb b
  simpa only [fieldCurvatureTransform, zero_mul, add_zero, fieldBiasCurvature, fieldBiasMean] using hh

lemma magneticCurvature_le_spin_variance (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    magneticCurvature h s ≤ 1 - s ^ 2 := by
  have hh := fieldBiasCurvature_le_spin_variance h (magneticBias h s)
  rwa [fieldBiasMean_magneticBias h hs] at hh

end InvariantIsing

end

end OAI
