import OAI.Analysis.IrrationalRotation.Sampling.FourierSampling

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.CircleKernelConvolution

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  norm_num
  infer_instance

def convolution (k : C(UnitAddCircle, ℝ)) (f : UnitAddCircle → ℝ)
    (x : UnitAddCircle) : ℝ := ∫ y, k (x - y) * f y

theorem integrable_unit_bounded {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) : Integrable f volume := by
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hf1 x

theorem integrable_kernel (k : C(UnitAddCircle, ℝ)) : Integrable k volume := by
  apply Integrable.of_bound k.measurable.aestronglyMeasurable ‖k‖
  exact Filter.Eventually.of_forall k.norm_coe_le_norm

theorem integrable_convolution_integrand (k : C(UnitAddCircle, ℝ))
    {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (x : UnitAddCircle) :
    Integrable (fun y => k (x - y) * f y) volume := by
  apply Integrable.of_bound
    ((k.measurable.comp (measurable_const.sub measurable_id)).mul hf).aestronglyMeasurable ‖k‖
  filter_upwards with y
  change ‖k (x - y) * f y‖ ≤ ‖k‖
  rw [norm_mul, Real.norm_eq_abs (f y), abs_of_nonneg (hf0 y)]
  calc
    ‖k (x - y)‖ * f y ≤ ‖k (x - y)‖ * 1 :=
      mul_le_mul_of_nonneg_left (hf1 y) (norm_nonneg _)
    _ ≤ ‖k‖ := by simpa using k.norm_coe_le_norm (x - y)

theorem convolution_bounds (k : C(UnitAddCircle, ℝ))
    (hk0 : ∀ x, 0 ≤ k x) (hkmass : ∫ x, k x = 1)
    {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (x : UnitAddCircle) :
    0 ≤ convolution k f x ∧ convolution k f x ≤ 1 := by
  constructor
  · exact integral_nonneg fun y => mul_nonneg (hk0 _) (hf0 _)
  · have hki : Integrable (fun y => k (x - y)) volume := by
      apply Integrable.of_bound
        (k.measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable ‖k‖
      exact Filter.Eventually.of_forall fun y => k.norm_coe_le_norm _
    calc
      convolution k f x ≤ ∫ y, k (x - y) := by
        apply integral_mono (integrable_convolution_integrand k hf hf0 hf1 x) hki
        intro y
        exact mul_le_of_le_one_right (hk0 _) (hf1 _)
      _ = ∫ y, k y := integral_sub_left_eq_self k volume x
      _ = 1 := hkmass

theorem integrable_joint (k : C(UnitAddCircle, ℝ))
    {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    Integrable (fun p : UnitAddCircle × UnitAddCircle => k (p.1 - p.2) * f p.2)
      (volume.prod volume) := by
  apply Integrable.of_bound
    ((k.measurable.comp (measurable_fst.sub measurable_snd)).mul
      (hf.comp measurable_snd)).aestronglyMeasurable ‖k‖
  filter_upwards with p
  change ‖k (p.1 - p.2) * f p.2‖ ≤ ‖k‖
  rw [norm_mul, Real.norm_eq_abs (f p.2), abs_of_nonneg (hf0 p.2)]
  calc
    ‖k (p.1 - p.2)‖ * f p.2 ≤ ‖k (p.1 - p.2)‖ * 1 :=
      mul_le_mul_of_nonneg_left (hf1 _) (norm_nonneg _)
    _ ≤ ‖k‖ := by simpa using k.norm_coe_le_norm _

theorem integral_convolution (k : C(UnitAddCircle, ℝ))
    (hkmass : ∫ x, k x = 1) {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    (∫ x, convolution k f x) = ∫ x, f x := by
  unfold convolution
  rw [integral_integral_swap (integrable_joint k hf hf0 hf1)]
  simp_rw [integral_mul_const]
  simp_rw [integral_sub_right_eq_self k, hkmass, one_mul]

theorem fourier_sub_argument (v : ℤ) (x y : UnitAddCircle) :
    fourier v (x - y) = fourier v x * fourier (-v) y := by
  simp [fourier_apply, sub_eq_add_neg, AddCircle.toCircle_add]

def testCoefficient (f : UnitAddCircle → ℝ) (v : ℤ) : ℂ :=
  ∫ y, fourier (-v) y * (f y : ℂ)

theorem integrable_test_character {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (v : ℤ) :
    Integrable (fun y => fourier v y * (f y : ℂ)) volume := by
  apply Integrable.of_bound
    ((fourier v).measurable.mul (Complex.measurable_ofReal.comp hf)).aestronglyMeasurable 1
  filter_upwards with y
  have hv : ‖fourier v y‖ = 1 := by simp [fourier_apply]
  change ‖fourier v y * (f y : ℂ)‖ ≤ 1
  rw [norm_mul, hv, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 y)]
  exact hf1 y

theorem norm_testCoefficient_le_one {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (v : ℤ) :
    ‖testCoefficient f v‖ ≤ 1 := by
  apply (norm_integral_le_integral_norm _).trans
  have h := integral_mono (integrable_test_character hf hf0 hf1 (-v)).norm
    (integrable_const (1 : ℝ)) (fun y => ?_)
  · simpa using h
  · have hv : ‖fourier (-v) y‖ = 1 := by simp [fourier_apply]
    rw [norm_mul, hv, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 y)]
    exact hf1 y

@[simp] theorem testCoefficient_zero (f : UnitAddCircle → ℝ) :
    testCoefficient f 0 = (∫ y, f y : ℝ) := by
  simp [testCoefficient, integral_complex_ofReal]

theorem convolution_eq_polynomial (k : C(UnitAddCircle, ℝ))
    (s : Finset ℤ) (c : ℤ → ℂ)
    (hk : ∀ x, (k x : ℂ) = FourierSampling.polynomial s c x)
    {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (x : UnitAddCircle) :
    (convolution k f x : ℂ) = FourierSampling.polynomial s
      (fun v => c v * testCoefficient f v) x := by
  rw [convolution, ← integral_complex_ofReal]
  simp_rw [Complex.ofReal_mul, hk, FourierSampling.polynomial, Finset.sum_mul]
  have hterm : ∀ v, Integrable (fun y => c v * fourier v (x - y) * (f y : ℂ)) volume := by
    intro v
    have he : (fun y => c v * fourier v (x - y) * (f y : ℂ)) =
        (fun y => (c v * fourier v x) * (fourier (-v) y * (f y : ℂ))) := by
      funext y
      rw [fourier_sub_argument]
      ring
    rw [he]
    exact (integrable_test_character hf hf0 hf1 (-v)).const_mul _
  rw [integral_finsetSum s (fun v hv => hterm v)]
  apply Finset.sum_congr rfl
  intro v hv
  simp_rw [fourier_sub_argument]
  have he : (fun y => c v * (fourier v x * fourier (-v) y) * (f y : ℂ)) =
      (fun y => (c v * fourier v x) * (fourier (-v) y * (f y : ℂ))) := by
    funext y
    ring
  rw [he, integral_const_mul]
  unfold testCoefficient
  ring

def translationError (f : UnitAddCircle → ℝ) (t : UnitAddCircle) : ℝ :=
  ∫ x, |f (x - t) - f x|

theorem translationError_nonneg (f : UnitAddCircle → ℝ) (t : UnitAddCircle) :
    0 ≤ translationError f t := integral_nonneg fun _ => abs_nonneg _

theorem translationError_le_one {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (t : UnitAddCircle) :
    translationError f t ≤ 1 := by
  have hb : ∀ x, |f (x - t) - f x| ≤ 1 := by
    intro x
    rw [abs_sub_le_iff]
    constructor <;> linarith [hf0 x, hf0 (x - t), hf1 x, hf1 (x - t)]
  have hi : Integrable (fun x => |f (x - t) - f x|) volume := by
    apply Integrable.of_bound
      (((hf.comp (measurable_id.sub measurable_const)).sub hf).abs).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x
  have h := integral_mono hi (integrable_const (1 : ℝ)) hb
  simpa [translationError] using h

theorem convolution_eq_shift (k : C(UnitAddCircle, ℝ)) (f : UnitAddCircle → ℝ)
    (x : UnitAddCircle) : convolution k f x = ∫ t, k t * f (x - t) := by
  have h := integral_sub_left_eq_self (fun y => k (x - y) * f y) volume x
  simpa [convolution, sub_sub_cancel] using h.symm

theorem convolution_error_pointwise_le (k : C(UnitAddCircle, ℝ))
    (hk0 : ∀ t, 0 ≤ k t) (hkmass : ∫ t, k t = 1)
    {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (x : UnitAddCircle) :
    |convolution k f x - f x| ≤ ∫ t, k t * |f (x - t) - f x| := by
  have hi : Integrable (fun t => k t * f (x - t)) volume := by
    apply Integrable.of_bound
      (k.measurable.mul (hf.comp (measurable_const.sub measurable_id))).aestronglyMeasurable ‖k‖
    filter_upwards with t
    change ‖k t * f (x - t)‖ ≤ ‖k‖
    rw [norm_mul, Real.norm_eq_abs (f (x - t)), abs_of_nonneg (hf0 _)]
    calc
      ‖k t‖ * f (x - t) ≤ ‖k t‖ * 1 := mul_le_mul_of_nonneg_left (hf1 _) (norm_nonneg _)
      _ ≤ ‖k‖ := by simpa using k.norm_coe_le_norm t
  have he : convolution k f x - f x = ∫ t, k t * (f (x - t) - f x) := by
    rw [convolution_eq_shift]
    have hc : (∫ t, k t * f x) = f x := by rw [integral_mul_const, hkmass, one_mul]
    calc
      (∫ t, k t * f (x - t)) - f x =
          (∫ t, k t * f (x - t)) - ∫ t, k t * f x := by rw [hc]
      _ = ∫ t, k t * f (x - t) - k t * f x :=
        (integral_sub hi ((integrable_kernel k).mul_const _)).symm
      _ = _ := by congr 1; funext t; ring
  rw [he]
  have h := norm_integral_le_integral_norm (μ := (volume : Measure UnitAddCircle)) (fun t => k t * (f (x - t) - f x))
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 _)] using h

theorem integrable_joint_error (k : C(UnitAddCircle, ℝ))
    {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    Integrable (fun p : UnitAddCircle × UnitAddCircle =>
      k p.2 * |f (p.1 - p.2) - f p.1|) (volume.prod volume) := by
  apply Integrable.of_bound ((k.measurable.comp measurable_snd).mul
    (((hf.comp (measurable_fst.sub measurable_snd)).sub (hf.comp measurable_fst)).abs)).aestronglyMeasurable ‖k‖
  filter_upwards with p
  change ‖k p.2 * |f (p.1 - p.2) - f p.1|‖ ≤ ‖k‖
  have hb : |f (p.1 - p.2) - f p.1| ≤ 1 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hf0 p.1, hf0 (p.1 - p.2), hf1 p.1, hf1 (p.1 - p.2)]
  simp only [norm_mul, Real.norm_eq_abs, abs_abs]
  calc
    ‖k p.2‖ * |f (p.1 - p.2) - f p.1| ≤ ‖k p.2‖ * 1 :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ ≤ ‖k‖ := by simpa using k.norm_coe_le_norm p.2

theorem l1_error_le_translation_average (k : C(UnitAddCircle, ℝ))
    (hk0 : ∀ t, 0 ≤ k t) (hkmass : ∫ t, k t = 1)
    {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    (∫ x, |convolution k f x - f x|) ≤ ∫ t, k t * translationError f t := by
  calc
    _ ≤ ∫ x, ∫ t, k t * |f (x - t) - f x| := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (integrable_joint_error k hf hf0 hf1).integral_prod_left
      exact Filter.Eventually.of_forall (convolution_error_pointwise_le k hk0 hkmass hf hf0 hf1)
    _ = ∫ t, ∫ x, k t * |f (x - t) - f x| :=
      integral_integral_swap (integrable_joint_error k hf hf0 hf1)
    _ = _ := by simp_rw [integral_const_mul, translationError]

theorem l1_error_le_small_translation_and_tail (k : C(UnitAddCircle, ℝ))
    (hk0 : ∀ t, 0 ≤ k t) (hkmass : ∫ t, k t = 1)
    {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    {B : Set UnitAddCircle} (hB : MeasurableSet B) {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hsmall : ∀ t ∈ B, translationError f t ≤ δ)
    (htail : (∫ t in Bᶜ, k t) ≤ ε) :
    (∫ x, |convolution k f x - f x|) ≤ δ + ε := by
  apply (l1_error_le_translation_average k hk0 hkmass hf hf0 hf1).trans
  calc
    (∫ t, k t * translationError f t) ≤ ∫ t, δ * k t + Bᶜ.indicator k t := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun t => mul_nonneg (hk0 t) (translationError_nonneg f t))
        (((integrable_kernel k).const_mul δ).add ((integrable_kernel k).indicator hB.compl))
      filter_upwards with t
      change k t * translationError f t ≤ δ * k t + Bᶜ.indicator k t
      by_cases ht : t ∈ B
      · rw [Set.indicator_of_notMem (show t ∉ Bᶜ from fun h => h ht), add_zero]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left (hsmall t ht) (hk0 t)
      · rw [Set.indicator_of_mem (Set.mem_compl ht)]
        have h₁ := mul_le_mul_of_nonneg_left (translationError_le_one hf hf0 hf1 t) (hk0 t)
        have h₂ := mul_nonneg hδ (hk0 t)
        nlinarith
    _ = δ + ∫ t in Bᶜ, k t := by
      rw [integral_add ((integrable_kernel k).const_mul δ)
        ((integrable_kernel k).indicator hB.compl), integral_const_mul,
        hkmass, mul_one, integral_indicator hB.compl]
    _ ≤ δ + ε := add_le_add le_rfl htail

end Invariant233.CircleKernelConvolution

end

end OAI
