import Mathlib
import OAI.Probability.Perceptron.Pressure.TerminalVariational

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma controlValue_trial_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) :
    controlValue P f m - controlValue P f n ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  suffices controlValue P f m ≤ controlValue P f n +
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw by linarith
  apply controlValue_le_of_bounded_controls P f m L hf
  intro v hv _ hbound
  have hpay : controlPayoff P f n v ≤ controlValue P f n :=
    le_csSup (controlPayoffs_bddAbove P f n) ⟨v, hv,
      (controlCost_le_bound P n L hbound).trans_lt (by finiteness), rfl⟩
  have hd := (abs_le.mp (controlPayoff_trial_diff_bound P f m n L hf hv hbound)).2
  linarith

lemma controlValue_trial_abs_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) :
    |controlValue P f m - controlValue P f n| ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  have hmn := controlValue_trial_sub_le P f m n L hf
  have hnm := controlValue_trial_sub_le P f n m L hf
  simp_rw [abs_sub_comm (n _) (m _)] at hnm
  exact abs_le.mpr ⟨by linarith, hmn⟩

lemma usual_measurable_aemeasurable (P : Measure BrownianPath) (t : Time)
    {Y : BrownianPath → ℝ} (hY : @Measurable _ _ (usualBrownianSigma P t) (borel ℝ) Y) :
    AEMeasurable Y P := by
  have h : NullMeasurable Y P := hY.mono (usualBrownianSigma_le_completion P t) le_rfl
  exact h.aemeasurable

lemma brownian_increment_indep_adapted (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (t : Time) (r : ℝ≥0) (htr : (t : ℝ) < r)
    {Y : BrownianPath → ℝ} (hY : @Measurable _ _ (usualBrownianSigma P t) (borel ℝ) Y) :
    IndepFun Y (fun ω => brownianEval r ω - brownianEval ⟨t.val, (show 0 ≤ (t : ℝ) from t.property.1)⟩ ω) P :=
  indep_of_indep_of_le_left (brownian_increment_indep_usual P hB t r htr) hY.comap_le

lemma second_order_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (C : ℝ) (hC : ∀ x, |iteratedDeriv 3 f x| ≤ C) (x y : ℝ) :
    |f y - f x - deriv f x * (y-x) - iteratedDeriv 2 f x * (y-x)^2/2| ≤
      C * |y-x|^3 / 6 := by
  by_cases hxy : x = y
  · subst y; simp
  have hs := uniqueDiffOn_uIcc hxy
  have hd₁ : iteratedDerivWithin 1 f (uIcc x y) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc, iteratedDeriv_one]
  have hd₂ : iteratedDerivWithin 2 f (uIcc x y) x = iteratedDeriv 2 f x :=
    iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc
  have hp : taylorWithinEval f 2 (uIcc x y) x y =
      f x + deriv f x * (y-x) + iteratedDeriv 2 f x * (y-x)^2/2 := by
    rw [show (2 : ℕ) = 1+1 from rfl, taylorWithinEval_succ,
      taylorWithinEval_succ, taylor_within_zero_eval, hd₁, hd₂]
    norm_num
    ring
  obtain ⟨z, -, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hxy hf.contDiffOn
  rw [hp] at hz
  have he : f y - f x - deriv f x * (y-x) - iteratedDeriv 2 f x * (y-x)^2/2 =
      iteratedDeriv 3 f z * (y-x)^3/6 := by
    norm_num at hz
    linarith only [hz]
  rw [he, abs_div, abs_mul, abs_pow]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hC z) (by positivity)) (by norm_num)

lemma first_order_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ) (hC : ∀ x, |iteratedDeriv 2 f x| ≤ C) (x y : ℝ) :
    |f y - f x - deriv f x * (y-x)| ≤ C * (y-x)^2 / 2 := by
  by_cases hxy : x = y
  · subst y; simp
  have hs := uniqueDiffOn_uIcc hxy
  have hd : iteratedDerivWithin 1 f (uIcc x y) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc, iteratedDeriv_one]
  have hp : taylorWithinEval f 1 (uIcc x y) x y = f x + deriv f x * (y-x) := by
    rw [show (1 : ℕ) = 0+1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval, hd]
    norm_num
    ring
  obtain ⟨z, -, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy hf.contDiffOn
  rw [hp] at hz
  have he : f y - f x - deriv f x * (y-x) = iteratedDeriv 2 f z * (y-x)^2/2 := by
    norm_num at hz
    linarith only [hz]
  rw [he, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (y-x))]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hC z) (sq_nonneg _)) (by norm_num)

lemma smooth_deriv_lipschitz {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ≥0) (hC : ∀ x, |iteratedDeriv 2 f x| ≤ C) : LipschitzWith C (deriv f) := by
  apply lipschitzWith_of_nnnorm_deriv_le hf.differentiable_deriv_two
  intro x
  apply NNReal.coe_le_coe.mp
  simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero, coe_nnnorm, Real.norm_eq_abs] using hC x

lemma drift_shift_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ≥0) (hC : ∀ x, |iteratedDeriv 2 f x| ≤ C) (x z a : ℝ) :
    |f (x+z+a) - f (x+z) - deriv f x * a| ≤ (C : ℝ) * (|z| * |a| + a^2/2) := by
  have ht := first_order_taylor_bound hf C hC (x+z) (x+z+a)
  simp only [add_sub_cancel_left] at ht
  have hd := (smooth_deriv_lipschitz hf C hC).dist_le_mul (x+z) x
  simp only [Real.dist_eq, add_sub_cancel_left] at hd
  calc
    _ = |(f (x+z+a) - f (x+z) - deriv f (x+z) * a) + (deriv f (x+z) - deriv f x) * a| := by congr 1; ring
    _ ≤ |f (x+z+a) - f (x+z) - deriv f (x+z) * a| + |(deriv f (x+z) - deriv f x) * a| := abs_add_le _ _
    _ ≤ (C : ℝ) * a^2/2 + (C : ℝ) * |z| * |a| := by
      rw [abs_mul]
      exact add_le_add ht (mul_le_mul_of_nonneg_right hd (abs_nonneg _))
    _ = _ := by ring

lemma gaussian_abs_moment (v : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, |x| ^ n ∂gaussianReal 0 v) =
      (Real.sqrt v)^n * ∫ x : ℝ, |x| ^ n ∂gaussianReal 0 1 := by
  have hv : (⟨(Real.sqrt v)^2, sq_nonneg _⟩ : ℝ≥0) = v := by
    ext; exact Real.sq_sqrt v.coe_nonneg
  have hL := gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt v)
  simp only [mul_zero, NNReal.mk] at hL
  rw [hv, mul_one] at hL
  rw [← hL.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|^n) (gaussianReal 0 v))]
  simp only [Function.comp_apply, id_eq, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  exact integral_const_mul _ _

lemma gaussian_law_integrable_abs_pow {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ} {v : ℝ≥0} (hZ : HasLaw Z (gaussianReal 0 v) P) (n : ℕ) :
    Integrable (fun ω => |Z ω|^n) P := by
  have hm : MemLp id (n : ℝ≥0∞) (gaussianReal 0 v) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := v) (n : ℝ≥0))
  have hi : Integrable (fun x : ℝ => |x|^n) (Measure.map Z P) := by
    rw [hZ.map_eq]
    simpa only [Real.norm_eq_abs, id_eq] using hm.integrable_norm_pow'
  exact (integrable_map_measure hi.aestronglyMeasurable hZ.aemeasurable).mp hi

lemma gaussian_law_sq_mean {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ} {v : ℝ≥0} (hZ : HasLaw Z (gaussianReal 0 v) P) :
    (∫ ω, (Z ω)^2 ∂P) = v := by
  have hi := hZ.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x^2)
    (gaussianReal 0 v))
  have hv := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := v) 2)
  simp only [variance_id_gaussianReal, Pi.pow_apply, id_eq, integral_id_gaussianReal,
    zero_pow (by decide : 2 ≠ 0), sub_zero] at hv
  exact hi.trans hv.symm

lemma bounded_real_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {Y : Ω → ℝ} (hY : AEMeasurable Y P)
    (C : ℝ) (hC : ∀ᵐ ω ∂P, |Y ω| ≤ C) : Integrable Y P := by
  exact (integrable_const C).mono' hY.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hC)

lemma boundedContinuousFunction_integrable_comp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] (f : ℝ →ᵇ ℝ) {X : Ω → ℝ}
    (hX : AEMeasurable X P) : Integrable (fun ω => f (X ω)) P := by
  exact bounded_real_integrable (f.continuous.measurable.comp_aemeasurable hX) ‖f‖
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (X ω))

lemma gaussian_taylor_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ) (hf : ContDiff ℝ 3 (f : ℝ → ℝ))
    (C₁ C₂ C₃ : ℝ) (h₁ : ∀ x, |deriv (f : ℝ → ℝ) x| ≤ C₁)
    (h₂ : ∀ x, |iteratedDeriv 2 (f : ℝ → ℝ) x| ≤ C₂)
    (h₃ : ∀ x, |iteratedDeriv 3 (f : ℝ → ℝ) x| ≤ C₃)
    {X Z : Ω → ℝ} (hX : AEMeasurable X P) {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hI : IndepFun X Z P) :
    |(∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (v : ℝ)/2 * ∫ ω, iteratedDeriv 2 (f : ℝ → ℝ) (X ω) ∂P| ≤
      C₃/6 * (Real.sqrt v)^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 := by
  let d₁ := deriv (f : ℝ → ℝ)
  let d₂ := iteratedDeriv 2 (f : ℝ → ℝ)
  have hm₁ : Measurable d₁ := (hf.continuous_deriv (by norm_num)).measurable
  have hm₂ : Measurable d₂ := (hf.continuous_iteratedDeriv 2 (by norm_num)).measurable
  have hi₁ : Integrable (fun ω => d₁ (X ω) * Z ω) P := by
    have hz : Integrable Z P := by
      have hi := gaussian_law_integrable_abs_pow hZ 1
      exact (integrable_norm_iff hZ.aemeasurable.aestronglyMeasurable).mp (by
        simpa only [pow_one, Real.norm_eq_abs] using hi)
    apply hz.bdd_mul (hm₁.comp_aemeasurable hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply, d₁] using h₁ (X ω)
  have hi₂ : Integrable (fun ω => d₂ (X ω) * (Z ω)^2) P := by
    have hz : Integrable (fun ω => (Z ω)^2) P := by
      simpa only [sq_abs] using gaussian_law_integrable_abs_pow hZ 2
    apply hz.bdd_mul (hm₂.comp_aemeasurable hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply, d₂] using h₂ (X ω)
  have hv₁ : (∫ ω, d₁ (X ω) * Z ω ∂P) = 0 := by
    have hh := (hI.comp hm₁ measurable_id).integral_fun_mul_eq_mul_integral
      (hm₁.comp_aemeasurable hX).aestronglyMeasurable hZ.aemeasurable.aestronglyMeasurable
    have hz : (∫ ω, Z ω ∂P) = 0 := hZ.integral_eq.trans (integral_id_gaussianReal)
    simpa only [Function.comp_apply, id_eq, hz, mul_zero] using hh
  have hv₂ : (∫ ω, d₂ (X ω) * (Z ω)^2 ∂P) = (v : ℝ) * (∫ ω, d₂ (X ω) ∂P) := by
    have hh := (hI.comp hm₂ (measurable_id.pow_const 2)).integral_fun_mul_eq_mul_integral
      (hm₂.comp_aemeasurable hX).aestronglyMeasurable (hZ.aemeasurable.pow_const 2).aestronglyMeasurable
    simp only [Function.comp_apply, id_eq] at hh
    exact hh.trans (by rw [gaussian_law_sq_mean hZ, mul_comm])
  let R := fun ω => f (X ω + Z ω) - f (X ω) - d₁ (X ω) * Z ω - d₂ (X ω) * (Z ω)^2/2
  have hiR : Integrable R P :=
    (((boundedContinuousFunction_integrable_comp f (hX.add hZ.aemeasurable)).sub
      (boundedContinuousFunction_integrable_comp f hX)).sub hi₁).sub (hi₂.div_const 2)
  have hR : ∀ ω, |R ω| ≤ C₃/6 * |Z ω|^3 := by
    intro ω
    have hh := second_order_taylor_bound hf C₃ h₃ (X ω) (X ω + Z ω)
    simpa only [add_sub_cancel_left, R, d₁, d₂, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  have hbound : |∫ ω, R ω ∂P| ≤ C₃/6 * ∫ ω, |Z ω|^3 ∂P := by
    calc
      _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, C₃/6 * |Z ω|^3 ∂P := integral_mono hiR.abs
        ((gaussian_law_integrable_abs_pow hZ 3).const_mul _) hR
      _ = _ := integral_const_mul _ _
  have he : (∫ ω, R ω ∂P) = (∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (v : ℝ)/2 * ∫ ω, d₂ (X ω) ∂P := by
    have ha := boundedContinuousFunction_integrable_comp f (hX.add hZ.aemeasurable)
    have hb := boundedContinuousFunction_integrable_comp f hX
    have he₁ := integral_sub ((ha.sub hb).sub hi₁) (hi₂.div_const 2)
    have he₂ := integral_sub (ha.sub hb) hi₁
    have he₃ := integral_sub ha hb
    simp only [Pi.add_apply, Pi.sub_apply] at he₁ he₂ he₃
    dsimp only [R]
    rw [he₁, he₂, he₃, integral_div, hv₁, hv₂]
    ring
  have hg : (∫ ω, |Z ω|^3 ∂P) = (Real.sqrt v)^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 :=
    (hZ.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|^3) (gaussianReal 0 v))).trans
      (gaussian_abs_moment v 3)
  rw [he, hg] at hbound
  exact hbound.trans_eq (by ring)

lemma drift_shift_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    (C₁ : ℝ) (C₂ K : ℝ≥0) (h₁ : ∀ x, |deriv (f : ℝ → ℝ) x| ≤ C₁)
    (h₂ : ∀ x, |iteratedDeriv 2 (f : ℝ → ℝ) x| ≤ C₂)
    {X Z A : Ω → ℝ} (hX : AEMeasurable X P) {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hA : AEMeasurable A P)
    (hAK : ∀ ω, |A ω| ≤ K) :
    |(∫ ω, f (X ω + Z ω + A ω) ∂P) - (∫ ω, f (X ω + Z ω) ∂P) -
      (∫ ω, deriv (f : ℝ → ℝ) (X ω) * A ω ∂P)| ≤
      (C₂ : ℝ) * ((K : ℝ) * Real.sqrt v * (∫ x : ℝ, |x| ∂gaussianReal 0 1) + (K : ℝ)^2/2) := by
  let d₁ := deriv (f : ℝ → ℝ)
  have hm₁ : Measurable d₁ := (hf.continuous_deriv (by norm_num)).measurable
  have hiA := bounded_real_integrable hA K (Filter.Eventually.of_forall hAK)
  have hi₁ : Integrable (fun ω => d₁ (X ω) * A ω) P := by
    apply hiA.bdd_mul (hm₁.comp_aemeasurable hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, d₁] using h₁ (X ω)
  have ha := boundedContinuousFunction_integrable_comp f ((hX.add hZ.aemeasurable).add hA)
  have hb := boundedContinuousFunction_integrable_comp f (hX.add hZ.aemeasurable)
  let R := fun ω => f (X ω + Z ω + A ω) - f (X ω + Z ω) - d₁ (X ω) * A ω
  have hiR : Integrable R P := (ha.sub hb).sub hi₁
  have hR : ∀ ω, |R ω| ≤ (C₂ : ℝ) * (|Z ω| * (K : ℝ) + (K : ℝ)^2/2) := by
    intro ω
    apply (drift_shift_taylor_bound hf C₂ h₂ (X ω) (Z ω) (A ω)).trans
    apply mul_le_mul_of_nonneg_left _ C₂.coe_nonneg
    have hsq : A ω ^2 ≤ (K : ℝ)^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (A ω)) K.coe_nonneg).mpr (hAK ω)
    exact add_le_add (mul_le_mul_of_nonneg_left (hAK ω) (abs_nonneg _)) (by linarith)
  have hiz : Integrable (fun ω => |Z ω|) P := by
    simpa only [pow_one] using gaussian_law_integrable_abs_pow hZ 1
  have hbound : |∫ ω, R ω ∂P| ≤
      (C₂ : ℝ) * ((∫ ω, |Z ω| ∂P) * (K : ℝ) + (K : ℝ)^2/2) := by
    calc
      _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (C₂ : ℝ) * (|Z ω| * (K : ℝ) + (K : ℝ)^2/2) ∂P :=
        integral_mono hiR.abs (((hiz.mul_const K).add (integrable_const _)).const_mul C₂) hR
      _ = _ := by rw [integral_const_mul, integral_add (hiz.mul_const K) (integrable_const _), integral_mul_const]; simp
  have he : (∫ ω, R ω ∂P) = (∫ ω, f (X ω + Z ω + A ω) ∂P) -
      (∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, d₁ (X ω) * A ω ∂P) := by
    have he₁ := integral_sub (ha.sub hb) hi₁
    have he₂ := integral_sub ha hb
    simp only [Pi.add_apply, Pi.sub_apply] at he₁ he₂
    exact he₁.trans (by rw [he₂])
  have hg : (∫ ω, |Z ω| ∂P) = Real.sqrt v * ∫ x : ℝ, |x| ∂gaussianReal 0 1 := by
    have hh := (hZ.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|^1) (gaussianReal 0 v))).trans
      (gaussian_abs_moment v 1)
    simpa only [pow_one, Function.comp_apply] using hh
  rw [he, hg] at hbound
  exact hbound.trans_eq (by ring)

lemma gaussian_drift_taylor_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ) (hf : ContDiff ℝ 3 (f : ℝ → ℝ))
    (C₁ C₃ : ℝ) (C₂ K : ℝ≥0) (h₁ : ∀ x, |deriv (f : ℝ → ℝ) x| ≤ C₁)
    (h₂ : ∀ x, |iteratedDeriv 2 (f : ℝ → ℝ) x| ≤ C₂)
    (h₃ : ∀ x, |iteratedDeriv 3 (f : ℝ → ℝ) x| ≤ C₃)
    {X Z A : Ω → ℝ} (hX : AEMeasurable X P) {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hI : IndepFun X Z P) (hA : AEMeasurable A P)
    (hAK : ∀ ω, |A ω| ≤ K) :
    |(∫ ω, f (X ω + Z ω + A ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (∫ ω, deriv (f : ℝ → ℝ) (X ω) * A ω ∂P) -
      (v : ℝ)/2 * ∫ ω, iteratedDeriv 2 (f : ℝ → ℝ) (X ω) ∂P| ≤
      (C₂ : ℝ) * ((K : ℝ) * Real.sqrt v * (∫ x : ℝ, |x| ∂gaussianReal 0 1) + (K : ℝ)^2/2) +
      C₃/6 * (Real.sqrt v)^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 := by
  have hG := gaussian_taylor_mean_bound f hf C₁ C₂ C₃ h₁ h₂ h₃ hX hZ hI
  have hD := drift_shift_mean_bound f (hf.of_le (by norm_num)) C₁ C₂ K h₁ h₂ hX hZ hA hAK
  have hh := abs_add_le
    ((∫ ω, f (X ω + Z ω + A ω) ∂P) - (∫ ω, f (X ω + Z ω) ∂P) -
      (∫ ω, deriv (f : ℝ → ℝ) (X ω) * A ω ∂P))
    ((∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (v : ℝ)/2 * ∫ ω, iteratedDeriv 2 (f : ℝ → ℝ) (X ω) ∂P)
  convert hh.trans (add_le_add hD hG) using 1
  congr 1
  ring

def gaussianAverage (s : ℝ≥0) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, f (x + z) ∂gaussianReal 0 s

lemma gaussianAverage_integrable (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    Integrable (fun z => f (x + z)) (gaussianReal 0 s) :=
  boundedContinuousFunction_integrable_comp f (by fun_prop)

lemma gaussianAverage_abs_le (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    |gaussianAverage s f x| ≤ ‖f‖ := by
  simpa [gaussianAverage, Real.norm_eq_abs] using
    norm_integral_le_of_norm_le_const (μ := gaussianReal 0 s)
      (Filter.Eventually.of_forall fun z => f.norm_coe_le_norm (x+z))

lemma gaussianAverage_continuous (s : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    Continuous (gaussianAverage s f) := by
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro x; exact (gaussianAverage_integrable s f x).aestronglyMeasurable
  · intro x; exact Filter.Eventually.of_forall fun z => f.norm_coe_le_norm (x+z)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun z => f.continuous.comp (continuous_id.add continuous_const)

def gaussianAverageBCF (s : ℝ≥0) (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨gaussianAverage s f, gaussianAverage_continuous s f⟩
    (2*‖f‖) (by
      intro x y
      change |gaussianAverage s f x - gaussianAverage s f y| ≤ 2 * ‖f‖
      exact (abs_sub _ _).trans (by linarith [gaussianAverage_abs_le s f x, gaussianAverage_abs_le s f y]))

@[simp] lemma gaussianAverageBCF_coe (s : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    (gaussianAverageBCF s f : ℝ → ℝ) = gaussianAverage s f := rfl

@[simp] lemma gaussianAverage_zero (f : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage 0 f x = f x := by simp [gaussianAverage]

lemma gaussianAverage_semigroup (s t : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage s (gaussianAverageBCF t f) x = gaussianAverage (s+t) f x := by
  have hi : Integrable (fun z => f (x+z)) ((gaussianReal 0 s) ∗ (gaussianReal 0 t)) := by
    rw [gaussianReal_conv_gaussianReal, zero_add]
    exact gaussianAverage_integrable (s+t) f x
  have hh := integral_conv hi
  simp only [gaussianReal_conv_gaussianReal, zero_add] at hh
  simpa only [gaussianAverage, gaussianAverageBCF_coe, add_assoc] using hh.symm

lemma gaussianAverage_hasDerivAt (s : ℝ≥0) (f f' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f : ℝ → ℝ) (f' x) x) (x : ℝ) :
    HasDerivAt (gaussianAverage s f) (gaussianAverage s f' x) x := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (F := fun x z => f (x+z)) (F' := fun x z => f' (x+z)) (bound := fun _ => ‖f'‖)
    (μ := gaussianReal 0 s) (by simp)
    (Filter.Eventually.of_forall fun x => (gaussianAverage_integrable s f x).aestronglyMeasurable)
    (gaussianAverage_integrable s f x)
    (gaussianAverage_integrable s f' x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z x _ => f'.norm_coe_le_norm (x+z)) (integrable_const _)
    (Filter.Eventually.of_forall fun z x _ => by convert! (hf (x+z)).comp x ((hasDerivAt_id x).add_const z) using 1; simp only [mul_one])).2

lemma gaussianAverage_deriv (s : ℝ≥0) (f f' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f : ℝ → ℝ) (f' x) x) :
    deriv (gaussianAverage s f) = gaussianAverage s f' := by
  funext x; exact (gaussianAverage_hasDerivAt s f f' hf x).deriv

lemma exp_bcf_bound (d : ℝ) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    |Real.exp (d * f x)| ≤ Real.exp (|d| * ‖f‖) := by
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    d * f x ≤ |d * f x| := le_abs_self _
    _ = |d| * |f x| := abs_mul _ _
    _ ≤ |d| * ‖f‖ := mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x) (abs_nonneg d)

def expBCF (d : ℝ) (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => Real.exp (d*f x), by fun_prop⟩
    (2 * Real.exp (|d| * ‖f‖)) (by
      intro x y; change |Real.exp (d * f x) - Real.exp (d * f y)| ≤ 2 * Real.exp (|d| * ‖f‖)
      exact (abs_sub _ _).trans (by linarith [exp_bcf_bound d f x, exp_bcf_bound d f y]))

@[simp] lemma expBCF_apply (d : ℝ) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    expBCF d f x = Real.exp (d * f x) := rfl

lemma gaussianAverage_exp_pos (s : ℝ≥0) (d : ℝ) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    0 < gaussianAverage s (expBCF d f) x := by
  apply integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos (d*f (x+z))).le)
    (gaussianAverage_integrable s (expBCF d f) x) |>.mpr
  simpa only [Function.support, expBCF_apply, ne_eq, Real.exp_ne_zero, not_false_eq_true,
    Set.ofPred_true, measure_univ] using (zero_lt_one : (0 : ℝ≥0∞) < 1)

lemma gaussianAverage_exp_bounds (s : ℝ≥0) (d : ℝ) (hd : 0 ≤ d) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    Real.exp (-d*‖f‖) ≤ gaussianAverage s (expBCF d f) x ∧
      gaussianAverage s (expBCF d f) x ≤ Real.exp (d*‖f‖) := by
  have hf : ∀ z, |f (x+z)| ≤ ‖f‖ := fun z => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (x+z)
  constructor
  · have hi := integral_mono (integrable_const (Real.exp (-d*‖f‖)))
      (gaussianAverage_integrable s (expBCF d f) x) (fun z =>
        Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp (hf z)).1]))
    simpa only [gaussianAverage, integral_const, probReal_univ, smul_eq_mul, one_mul] using hi
  · have hi := integral_mono (gaussianAverage_integrable s (expBCF d f) x)
      (integrable_const (Real.exp (d*‖f‖))) (fun z =>
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hf z)).2 hd))
    simpa only [gaussianAverage, integral_const, probReal_univ, smul_eq_mul, one_mul] using hi

def heatLog (s : ℝ≥0) (d : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) : ℝ :=
  if d = 0 then gaussianAverage s f x else (d : ℝ)⁻¹ * Real.log (gaussianAverage s (expBCF d f) x)

lemma heatLog_abs_le (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) : |heatLog s d f x| ≤ ‖f‖ := by
  unfold heatLog
  split_ifs with hd
  · exact gaussianAverage_abs_le s f x
  have hd' : (0 : ℝ) < d := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hd)
  obtain ⟨hlo,hhi⟩ := gaussianAverage_exp_bounds s d d.coe_nonneg f x
  have hz := gaussianAverage_exp_pos s d f x
  have hl := Real.log_le_log (Real.exp_pos _) hlo
  have hu := Real.log_le_log hz hhi
  rw [Real.log_exp] at hl hu
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hd'.le),
    mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hd'.le), inv_mul_cancel₀ hd'.ne']

end SphericalPerceptronFreeEnergy
end

end OAI
