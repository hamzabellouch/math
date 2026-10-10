import OAI.Probability.InvariantIsing.Magnetic.MagneticRelativeThird

namespace OAI

/-! A positive exponential lower bound for the actual finite-step curvature.
The constant depends only on the finite covariance data, not on the bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def magneticGaussianLowerFactor (ζ : ℝ) (v : ℝ≥0) : ℝ :=
  (∫ u : ℝ, Real.exp (-(|ζ| + 2) * |u|) ∂gaussianReal 0 v) /
    (∫ u : ℝ, Real.exp (|ζ| * |u|) ∂gaussianReal 0 v)

lemma magneticGaussianLowerFactor_pos (ζ : ℝ) (v : ℝ≥0) :
    0 < magneticGaussianLowerFactor ζ v := by
  have hp (a : ℝ) : 0 < ∫ u : ℝ, Real.exp (a * |u|) ∂gaussianReal 0 v := by
    have hi : Integrable (fun u : ℝ => Real.exp (a * |u|)) (gaussianReal 0 v) := by
      simpa only [Real.norm_eq_abs] using gaussianReal_exponentialNormMoments 0 v a
    exact (integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hi).mpr
      (by simp [Function.support, Real.exp_ne_zero])
  exact div_pos (hp _) (hp _)

lemma fieldSpinTransition_exponential_lower (ζ : ℝ) (v : ℝ≥0)
    {F Q : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hQ : Measurable Q) {B c : ℝ} (bQ : ∀ x, |Q x| ≤ B) (hc : 0 < c)
    (hlo : ∀ x, c * Real.exp (-2 * |x|) ≤ Q x)
    (hLip : ∀ x y, |F x - F y| ≤ |x - y|) (z : ℝ) :
    (c * magneticGaussianLowerFactor ζ v) * Real.exp (-2 * |z|) ≤
      fieldSpinTransition ζ v F Q z := by
  let μ := gaussianReal 0 v
  let H : ℝ → ℝ := fun u => ζ * F (z + u)
  let U : ℝ → ℝ := fun u => H u - ζ * F z
  have hmH : Measurable H := (hF.comp (measurable_const.add measurable_id)).const_mul ζ
  have hmU : Measurable U := hmH.sub_const _
  have hU (u : ℝ) : |U u| ≤ |ζ| * |u| := by
    have hl := hLip (z + u) z
    rw [add_sub_cancel_left] at hl
    calc
      |U u| = |ζ| * |F (z + u) - F z| := by
        dsimp only [U, H]
        rw [← mul_sub, abs_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (abs_nonneg ζ)
  have hexp (a : ℝ) : Integrable (fun u : ℝ => Real.exp (a * |u|)) μ := by
    simpa only [Real.norm_eq_abs] using gaussianReal_exponentialNormMoments 0 v a
  have hiU : Integrable (fun u => Real.exp (U u)) μ :=
    (hexp |ζ|).mono' hmU.exp.aestronglyMeasurable (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hU u)))
  have hprod : Integrable (fun u => Real.exp (U u) * Q (z + u)) μ :=
    hiU.mul_bdd (hQ.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using bQ (z + u))
  have hQP (x : ℝ) : 0 ≤ Q x :=
    (mul_pos hc (Real.exp_pos _)).le.trans (hlo x)
  have hnum : c * Real.exp (-2 * |z|) *
      (∫ u : ℝ, Real.exp (-(|ζ| + 2) * |u|) ∂μ) ≤
      ∫ u, Real.exp (U u) * Q (z + u) ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono ((hexp _).const_mul _) hprod
    intro u
    have hQlower : c * Real.exp (-2 * |z|) * Real.exp (-2 * |u|) ≤ Q (z + u) := by
      calc
        _ = c * Real.exp (-2 * (|z| + |u|)) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        _ ≤ c * Real.exp (-2 * |z + u|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [abs_add_le z u])) hc.le
        _ ≤ _ := hlo _
    have hUlower : Real.exp (-|ζ| * |u|) ≤ Real.exp (U u) :=
      Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hU u)).1])
    calc
      _ = Real.exp (-|ζ| * |u|) * (c * Real.exp (-2 * |z|) * Real.exp (-2 * |u|)) := by
        change c * Real.exp (-2 * |z|) * Real.exp (-(|ζ| + 2) * |u|) = _
        rw [show -(|ζ| + 2) * |u| = -|ζ| * |u| + (-2 * |u|) by ring, Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul hUlower hQlower (by positivity) (Real.exp_pos _).le
  have hden : (∫ u, Real.exp (U u) ∂μ) ≤ ∫ u : ℝ, Real.exp (|ζ| * |u|) ∂μ :=
    integral_mono hiU (hexp _) (fun u => Real.exp_le_exp.mpr ((le_abs_self _).trans (hU u)))
  have hdenpos : 0 < ∫ u, Real.exp (U u) ∂μ :=
    (integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hiU).mpr
      (by simp [Function.support, Real.exp_ne_zero, μ])
  have hH : Integrable (fun u => Real.exp (H u)) μ :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 v)
      (hF.comp (measurable_const.add measurable_id)) (hG.add_left z) ζ
  have : IsProbabilityMeasure (μ.tilted H) := isProbabilityMeasure_tilted hH
  have he : μ.tilted U = μ.tilted H := by
    have hh := tilted_tilted hH (fun _ => -(ζ * F z))
    simpa only [tilted_const, Pi.add_def, sub_eq_add_neg, U] using hh.symm
  rw [fieldSpinTransition_eq_shifted ζ v hF hQ, ← he, integral_tilted_eq_div]
  have hd := div_le_div₀ (integral_nonneg fun u => mul_nonneg (Real.exp_pos _).le (hQP _))
    hnum hdenpos hden
  convert hd using 1
  unfold magneticGaussianLowerFactor
  dsimp only [μ]
  ring

lemma fieldScalarLogCosh_lipschitz (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (x y : ℝ) :
    |fieldScalarValue L (fun z => Real.log (Real.cosh z)) x -
      fieldScalarValue L (fun z => Real.log (Real.cosh z)) y| ≤ |x - y| := by
  have hm : Measurable Real.tanh := by
    change Measurable (fun z : ℝ => Real.tanh z)
    simp only [Real.tanh_eq]
    fun_prop
  have hb := fieldScalarMean_regular L hL measurable_logCosh logCosh_linearGrowth
    hm field_abs_tanh_le_one
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z (_ : z ∈ (univ : Set ℝ)) => (hasDerivAt_fieldScalarLogCosh L hL z).hasDerivWithinAt)
      (fun z _ => by simpa only [Real.norm_eq_abs] using hb.2 z)
      convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using he

lemma field_logCosh_curvature_exponential_lower (z : ℝ) :
    Real.exp (-2 * |z|) ≤ 1 / (Real.cosh z) ^ 2 := by
  have hc : Real.cosh z ≤ Real.exp |z| := by
    rw [Real.cosh_eq]
    have hp := Real.exp_le_exp.mpr (le_abs_self z)
    have hm := Real.exp_le_exp.mpr (neg_le_abs z)
    linarith
  have hs := pow_le_pow_left₀ (Real.cosh_pos z).le hc 2
  rw [one_div]
  rw [show Real.exp (-2 * |z|) = (Real.exp |z| ^ 2)⁻¹ by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; ring]
  exact inv_anti₀ (sq_pos_of_pos (Real.cosh_pos z)) hs

def magneticCurvatureLowerCap : List (ℝ × ℝ≥0) → ℝ
  | [] => 1
  | av :: L => magneticCurvatureLowerCap L * magneticGaussianLowerFactor av.1 av.2

lemma magneticCurvatureLowerCap_pos (L : List (ℝ × ℝ≥0)) :
    0 < magneticCurvatureLowerCap L := by
  induction L with
  | nil => exact zero_lt_one
  | cons av L ih => exact mul_pos ih (magneticGaussianLowerFactor_pos _ _)

lemma fieldScalarLogCoshSecond_exponential_lower (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    magneticCurvatureLowerCap L * Real.exp (-2 * |z|) ≤
      fieldScalarSecond L (fun x => Real.log (Real.cosh x)) Real.tanh
        (fun x => 1 / (Real.cosh x) ^ 2) z := by
  induction L generalizing z with
  | nil => simpa only [magneticCurvatureLowerCap, one_mul, fieldScalarSecond] using
      field_logCosh_curvature_exponential_lower z
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hq := fieldScalarLogCoshSecond_regular L ht
    have hl := fieldSpinTransition_exponential_lower av.1 av.2 hv.1 hv.2 hq.1 hq.2
      (magneticCurvatureLowerCap_pos L) (ih ht) (fieldScalarLogCosh_lipschitz L ht) z
    have hm : Measurable Real.tanh := by
      change Measurable (fun x : ℝ => Real.tanh x)
      simp only [Real.tanh_eq]
      fun_prop
    have ha := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      hm field_abs_tanh_le_one
    have hvar := fieldSpinTransition_square_le av.1 av.2 hv.1 hv.2 ha.1 ha.2 z
    change magneticCurvatureLowerCap (av :: L) * Real.exp (-2 * |z|) ≤
      fieldSpinTransition av.1 av.2 _ _ z + av.1 *
        (fieldSpinTransition av.1 av.2 _ _ z - (fieldSpinTransition av.1 av.2 _ _ z) ^ 2)
    exact hl.trans (le_add_of_nonneg_right
      (mul_nonneg (hL av List.mem_cons_self).le (sub_nonneg.mpr hvar)))

lemma fieldBiasCurvature_exponential_lower (h : FieldStep) (b : ℝ) :
    (magneticCurvatureLowerCap (scalarFieldIncrements h) *
      magneticGaussianLowerFactor 0 (NNReal.mk (h.height 0) (h.nonneg 0))) *
        Real.exp (-2 * |b|) ≤ fieldBiasCurvature h b := by
  have hL := scalarFieldIncrements_positive h
  have hv := fieldScalarValue_regular _ hL measurable_logCosh logCosh_linearGrowth
  have hq := fieldScalarLogCoshSecond_regular _ hL
  exact fieldSpinTransition_exponential_lower 0 _ hv.1 hv.2 hq.1 hq.2
    (magneticCurvatureLowerCap_pos _) (fieldScalarLogCoshSecond_exponential_lower _ hL)
    (fieldScalarLogCosh_lipschitz _ hL) b

end InvariantIsing

end

end OAI
