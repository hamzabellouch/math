import OAI.Probability.InvariantIsing.Fields.FieldSpinLipschitz
import OAI.Probability.InvariantIsing.Fields.FieldGaussianTiltMoments

namespace OAI

/-! A quantitative conditional-variance bound for a Lipschitz spin
mean. The constant depends only on an upper bound for the Gaussian
variance, rather than on the depth of the scalar recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldGaussianMomentCap_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ fieldGaussianMomentCap C := by
  have hb := (field_centered_tilt_second_moment (U := fun _ => 0) measurable_const
    (C := C) (fun u => by simpa using mul_nonneg hC (abs_nonneg u))).2
  exact (integral_nonneg (fun u => sq_nonneg (1 + |u|))).trans hb

lemma field_centered_spin_variance {U M : ℝ → ℝ}
    (hU : Measurable U) (hM : Measurable M)
    (hMb : ∀ z, |M z| ≤ 1) (hML : ∀ x y, |M x - M y| ≤ |x - y|)
    {C : ℝ} (hUb : ∀ u, |U u| ≤ C * |u|) (x : ℝ) (v : ℝ≥0) :
    variance (fun u => M (x + Real.sqrt (v : ℝ) * u)) ((gaussianReal 0 1).tilted U) ≤
      (v : ℝ) * fieldGaussianMomentCap C := by
  let μ := (gaussianReal 0 1).tilted U
  have he : Integrable (fun u => Real.exp (U u)) (gaussianReal 0 1) := by
    apply (gaussianReal_exponentialNormMoments 0 1 C).mono' hU.exp.aestronglyMeasurable
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hUb u))
  let : IsProbabilityMeasure μ := isProbabilityMeasure_tilted he
  let X := fun u => M (x + Real.sqrt (v : ℝ) * u)
  have hmX : Measurable X := hM.comp (by fun_prop)
  have hmD : AEStronglyMeasurable (fun u => X u - M x) μ :=
    (hmX.sub_const _).aestronglyMeasurable
  have hLp : MemLp (fun u => X u - M x) 2 μ :=
    MemLp.of_bound hmD 2 (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (by dsimp only [X]; linarith [hMb (x + Real.sqrt (v : ℝ) * u), hMb x]))
  obtain ⟨hi, hb⟩ := field_centered_tilt_second_moment hU hUb
  have hp (u : ℝ) : (X u - M x)^2 ≤ (v : ℝ) * (1 + |u|)^2 := by
    have hl : |X u - M x| ≤ Real.sqrt (v : ℝ) * |u| := by
      simpa only [X, add_sub_cancel_left, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using
        hML (x + Real.sqrt (v : ℝ) * u) x
    have hs := pow_le_pow_left₀ (abs_nonneg _) hl 2
    rw [sq_abs, mul_pow, Real.sq_sqrt v.coe_nonneg] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg u) (by linarith : |u| ≤ 1 + |u|) 2) v.coe_nonneg)
  calc
    variance X μ = variance (fun u => X u - M x) μ :=
      (variance_sub_const hmX.aestronglyMeasurable (M x)).symm
    _ ≤ ∫ u, (X u - M x)^2 ∂μ := variance_le_expectation_sq hmD
    _ ≤ ∫ u, (v : ℝ) * (1 + |u|)^2 ∂μ := integral_mono hLp.integrable_sq (hi.const_mul _) hp
    _ = (v : ℝ) * ∫ u, (1 + |u|)^2 ∂μ := integral_const_mul _ _
    _ ≤ (v : ℝ) * fieldGaussianMomentCap C := mul_le_mul_of_nonneg_left hb v.coe_nonneg

lemma fieldSpinTransition_centered_standard (ζ : ℝ) (v : ℝ≥0) {F M : ℝ → ℝ}
    (hF : Measurable F) (hM : Measurable M) (x : ℝ) :
    fieldSpinTransition ζ v F M x =
      ∫ u, M (x + Real.sqrt (v : ℝ) * u)
        ∂(gaussianReal 0 1).tilted (fun u => ζ * (F (x + Real.sqrt (v : ℝ) * u) - F x)) := by
  rw [fieldSpinTransition_eq_standard ζ v hF hM, gaussianTiltAverage_eq_div,
    integral_tilted_eq_div]
  simp_rw [mul_sub, Real.exp_sub, div_mul_eq_mul_div]
  rw [integral_div, integral_div, div_div_div_cancel_right₀ (Real.exp_ne_zero _)]

lemma fieldSpinTransition_variance_bound (ζ : ℝ) (v : ℝ≥0) {F M : ℝ → ℝ}
    (hF : Measurable F) (hM : Measurable M)
    (hMb : ∀ z, |M z| ≤ 1) (hML : ∀ x y, |M x - M y| ≤ |x - y|)
    (x : ℝ) {C : ℝ}
    (hUb : ∀ u, |ζ * (F (x + Real.sqrt (v : ℝ) * u) - F x)| ≤ C * |u|) :
    fieldSpinTransition ζ v F (fun z => (M z)^2) x -
        (fieldSpinTransition ζ v F M x)^2 ≤ (v : ℝ) * fieldGaussianMomentCap C := by
  let U := fun u => ζ * (F (x + Real.sqrt (v : ℝ) * u) - F x)
  have hU : Measurable U := by dsimp only [U]; fun_prop
  have he : Integrable (fun u => Real.exp (U u)) (gaussianReal 0 1) := by
    apply (gaussianReal_exponentialNormMoments 0 1 C).mono' hU.exp.aestronglyMeasurable
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hUb u))
  let μ := (gaussianReal 0 1).tilted U
  let : IsProbabilityMeasure μ := isProbabilityMeasure_tilted he
  have hm : Measurable (fun u => M (x + Real.sqrt (v : ℝ) * u)) := hM.comp (by fun_prop)
  have hLp : MemLp (fun u => M (x + Real.sqrt (v : ℝ) * u)) 2 μ :=
    MemLp.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun u => by
      simpa only [Real.norm_eq_abs] using hMb (x + Real.sqrt (v : ℝ) * u))
  rw [fieldSpinTransition_centered_standard ζ v hF (hM.pow_const 2),
    fieldSpinTransition_centered_standard ζ v hF hM]
  change (∫ u, (M (x + Real.sqrt (v : ℝ) * u))^2 ∂μ) -
    (∫ u, M (x + Real.sqrt (v : ℝ) * u) ∂μ)^2 ≤ _
  have heq := variance_eq_sub hLp
  simp only [Pi.pow_apply] at heq
  rw [← heq]
  exact field_centered_spin_variance hU hM hMb hML hUb x v

lemma fieldSpinTransition_variance_le (ζ : ℝ) (hζ : ζ ∈ Icc 0 1) (v : ℝ≥0)
    {V : ℝ} (hv : (v : ℝ) ≤ V) {F M : ℝ → ℝ}
    (hF : Measurable F) (hFL : ∀ x y, |F x - F y| ≤ |x - y|)
    (hM : Measurable M) (hMb : ∀ z, |M z| ≤ 1)
    (hML : ∀ x y, |M x - M y| ≤ |x - y|) (x : ℝ) :
    fieldSpinTransition ζ v F (fun z => (M z)^2) x -
      (fieldSpinTransition ζ v F M x)^2 ≤ (v : ℝ) * fieldGaussianMomentCap (Real.sqrt V) := by
  apply fieldSpinTransition_variance_bound ζ v hF hM hMb hML x
  intro u
  rw [abs_mul, abs_of_nonneg hζ.1]
  have hf : |F (x + Real.sqrt (v : ℝ) * u) - F x| ≤ Real.sqrt V * |u| := by
    have hh := hFL (x + Real.sqrt (v : ℝ) * u) x
    simp only [add_sub_cancel_left, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hv) (abs_nonneg u))
  exact (mul_le_mul_of_nonneg_left hf hζ.1).trans
    (mul_le_of_le_one_left (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hζ.2)

end InvariantIsing

end

end OAI
