import OAI.Analysis.Herglotz
import OAI.Analysis.DiagonalForms

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal

namespace EntropyPhotonNumber
open Herglotz MeasureTheory

theorem boundaryB_f_sq {x : ℝ} (hx : 0 ≤ x) :
    boundaryB ((f x ^ 2 : ℝ) : ℂ) = (b x : ℂ) := by
  have hf := f_pos x
  have hroot : Complex.sqrt ((f x ^ 2 : ℝ) : ℂ) = (f x : ℂ) := by
    rw [Complex.sqrt_of_nonneg (by exact_mod_cast (sq_nonneg (f x))), Complex.ofReal_re,
      Real.sqrt_sq hf.le]
  have hsin : sinhc x = (f x)⁻¹ := by
    rw [f_eq_inv_dslope, inv_inv]
    rfl
  have hz : (x : ℂ) * I ∈ closedSineDomain := by
    constructor
    · exact ⟨by simp, by simpa using Real.pi_pos.le, by simpa using hx⟩
    · change 0 < (csinc ((x : ℂ) * I)).re ∧ (csinc ((x : ℂ) * I)).im ≤ 0
      rw [csinc_mul_I, hsin]
      exact ⟨inv_pos.mpr hf, by simp⟩
  have hw : (f x : ℂ)⁻¹ ∈ closedSineQuadrant := by
    rw [← Complex.ofReal_inv]
    exact ⟨inv_pos.mpr hf, by simp⟩
  have hi : closedSineInverse ((f x : ℂ)⁻¹) = (x : ℂ) * I := by
    apply csinc_injOn_closedSineDomain (closedSineInverse_mem hw) hz
    rw [csinc_closedSineInverse hw, csinc_mul_I, hsin, Complex.ofReal_inv]
  rw [boundaryB, upperReflect_eq (by simp [-Complex.ofReal_pow]), hroot, hi, ccot, Complex.cos_mul_I,
    ← Complex.ofReal_cosh, csinc_mul_I, ← Complex.ofReal_div, hsin, div_inv_eq_mul]
  simp only [b, Complex.ofReal_mul, mul_comm]

theorem boundaryB_eq_B {s : ℝ} (hs : s ∈ Ioc 0 1) : boundaryB (s : ℂ) = (B s : ℂ) := by
  have he := boundaryB_f_sq (bParameter_nonneg hs)
  rw [f_sq_bParameter hs] at he
  exact he

theorem exists_B_resolvent : ∃ μ : FiniteMeasure Angle,
    (μ : Measure Angle) ≠ 0 ∧
    ∀ s : ℂ, 0 < s.im ∨ (s.im = 0 ∧ 0 < s.re) →
      boundaryB s = 1 - (s - 1) * compactIntegral μ s := by
  obtain ⟨μ, hμ⟩ := pick_divided_difference_of_continuous (P := fun s => -boundaryB s)
    (fun s hs => (analyticAt_boundaryB hs).neg)
    (fun s hs => by simpa using (boundaryB_im_neg hs).le)
    (fun x hx => ⟨(continuousAt_boundaryB hx).neg, by simp [boundaryB_real hx]⟩)
  have he (s : ℂ) (hs : 0 < s.im) : boundaryB s = 1 - (s - 1) * compactIntegral μ s := by
    have h := hμ s hs
    rw [boundaryB_one] at h
    linear_combination -h
  have hn : (μ : Measure Angle) ≠ 0 := by
    intro hz
    have h := he I (by simp)
    simp only [compactIntegral, hz, integral_zero_measure, mul_zero, sub_zero] at h
    have hi := boundaryB_im_neg (s := I) (by simp)
    simp [h] at hi
  refine ⟨μ, hn, ?_⟩
  intro s hs
  rcases hs with hs | ⟨hi, hr⟩
  · exact he s hs
  · have hb := upper_boundary_eq (continuousAt_boundaryB hr)
      (continuousAt_const.sub ((continuousAt_id.sub continuousAt_const).mul
        (continuousAt_compactIntegral μ hr))) he
    have hs : (s.re : ℂ) = s := (eq_of_im_zero hi).symm
    simpa only [Pi.sub_apply, Pi.mul_apply, id_eq, hs] using hb

end EntropyPhotonNumber

namespace EntropyPhotonNumber.Herglotz

theorem compactIntegral_re_pos (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0)
    {s : ℂ} (hs : 0 < s.re) : 0 < (compactIntegral μ s).re := by
  have hi := compactKernel_integrable μ (Or.inr hs)
  have hre : (compactIntegral μ s).re = ∫ θ : Angle,
      (compactKernel (boundaryParameter θ) (boundaryWeight θ) s).re ∂(μ : Measure Angle) :=
    (Complex.reCLM.integral_comp_comm hi).symm
  have hp (θ : Angle) : 0 < (compactKernel (boundaryParameter θ) (boundaryWeight θ) s).re := by
    have ht := boundaryParameter_mem θ
    have hd : 0 < (1 + (s - 1) * (boundaryParameter θ : ℂ)).re := by
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.sub_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      by_cases ha : boundaryParameter θ = 0
      · simp [ha]
      · nlinarith [mul_pos hs (lt_of_le_of_ne ht.1 (Ne.symm ha)), ht.2]
    simp only [compactKernel, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, zero_div, add_zero]
    exact div_pos (mul_pos (boundaryWeight_pos θ) hd)
      (Complex.normSq_pos.mpr (compactDen_ne_zero ht (Or.inr hs)))
  rw [hre, integral_pos_iff_support_of_nonneg (fun θ => (hp θ).le) (Complex.reCLM.integrable_comp hi)]
  have he : Function.support (fun θ : Angle =>
      (compactKernel (boundaryParameter θ) (boundaryWeight θ) s).re) = univ := by
    ext θ
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hp θ).ne'
  rw [he]
  exact Measure.measure_univ_pos.mpr hμ

end EntropyPhotonNumber.Herglotz

namespace EntropyPhotonNumber
open MeasureTheory Herglotz

def resolventB (μ : FiniteMeasure Angle) (s : ℂ) : ℂ :=
  1 - (s - 1) * compactIntegral μ s

def resolventR (μ : FiniteMeasure Angle) (s : ℂ) : ℂ :=
  (s * compactIntegral μ s)⁻¹

theorem analyticAt_resolventB (μ : FiniteMeasure Angle) {s : ℂ}
    (hs : 0 < s.im ∨ 0 < s.re) : AnalyticAt ℂ (resolventB μ) s :=
  analyticAt_const.sub ((analyticAt_id.sub analyticAt_const).mul (analyticAt_compactIntegral μ hs))

theorem analyticAt_resolventR (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0)
    {s : ℂ} (hs : 0 < s.im ∨ 0 < s.re) : AnalyticAt ℂ (resolventR μ) s := by
  apply ((analyticAt_id.mul (analyticAt_compactIntegral μ hs))).inv
  apply mul_ne_zero
  · intro h
    change s = 0 at h
    rcases hs with hs | hs <;> simp [h] at hs
  · rcases hs with hs | hs
    · exact compactIntegral_ne_zero μ hμ hs
    · intro h
      have hp := compactIntegral_re_pos μ hμ hs
      simp [h] at hp

theorem resolventR_im_nonpos (μ : FiniteMeasure Angle) {s : ℂ} (hs : 0 < s.im) :
    (resolventR μ s).im ≤ 0 := by
  rw [resolventR, Complex.inv_im]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_compactIntegral_im_nonneg μ hs))
    (Complex.normSq_nonneg _)

theorem resolventR_real (μ : FiniteMeasure Angle) (x : ℝ) : (resolventR μ (x : ℂ)).im = 0 := by
  rw [resolventR, compactIntegral_real, ← Complex.ofReal_mul, ← Complex.ofReal_inv]
  exact Complex.ofReal_im _

theorem resolventR_real_pos (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0)
    {x : ℝ} (hx : 0 < x) : 0 < (resolventR μ (x : ℂ)).re := by
  have hp := compactIntegral_real_pos μ hμ hx
  rw [resolventR, compactIntegral_real, ← Complex.ofReal_mul, ← Complex.ofReal_inv, Complex.ofReal_re]
  rw [compactIntegral_real, Complex.ofReal_re] at hp
  exact inv_pos.mpr (mul_pos hx hp)

theorem resolventR_stieltjes (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ν : FiniteMeasure Angle,
      ∀ x : ℝ, 0 < x → (resolventR μ (x : ℂ)).re = c +
        ∫ θ : Angle, (1 + (x - 1) * boundaryParameter θ)⁻¹ ∂(ν : Measure Angle) := by
  apply compact_stieltjes_representation
  · intro s hs
    exact analyticAt_resolventR μ hμ (Or.inl hs)
  · exact fun s hs => resolventR_im_nonpos μ hs
  · intro x hx
    exact ⟨analyticAt_resolventR μ hμ (Or.inr hx), resolventR_real μ x,
      (resolventR_real_pos μ hμ hx).le⟩

theorem analytic_eqOn_rightHalfPlane_of_real_interval {F K : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.re})
    (hK : AnalyticOnNhd ℂ K {z : ℂ | 0 < z.re})
    (he : ∀ x : ℝ, x ∈ Ioo 0 1 → F (x : ℂ) = K (x : ℂ)) :
    EqOn F K {z : ℂ | 0 < z.re} := by
  apply hF.eqOn_of_preconnected_of_mem_closure hK (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := (1 / 2 : ℂ)) (by norm_num)
  let xs : ℕ → ℝ := fun n => 1 / 2 + 1 / ((n : ℝ) + 3)
  have hxs (n : ℕ) : xs n ∈ Ioo 0 1 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp : 0 < 1 / ((n : ℝ) + 3) := by positivity
    have hlt : 1 / ((n : ℝ) + 3) < 1 / 2 := by
      exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)
    dsimp [xs]
    constructor <;> linarith
  have ht : Tendsto xs atTop (𝓝 (1 / 2)) := by
    have hd : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 3)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 3)
    simpa [xs] using (tendsto_const_nhds (x := (1 / 2 : ℝ))).add hd
  have htc : Tendsto (fun n => (xs n : ℂ)) atTop (𝓝 (1 / 2 : ℂ)) := by
    convert! Complex.continuous_ofReal.continuousAt.tendsto.comp ht using 1
    norm_num
  apply mem_closure_of_tendsto htc
  filter_upwards with n
  refine ⟨he (xs n) (hxs n), ?_⟩
  simp only [mem_singleton_iff]
  intro h
  have hreal := congrArg Complex.re h
  norm_num at hreal
  have hp : 0 < 1 / ((n : ℝ) + 3) := by positivity
  dsimp [xs] at hreal
  norm_num at hreal
  linarith

theorem deriv_resolventB_on_original (μ : FiniteMeasure Angle)
    (he : ∀ x : ℝ, x ∈ Ioc 0 1 → resolventB μ (x : ℂ) = (B x : ℂ))
    {x : ℝ} (hx : x ∈ Ioo 0 1) :
    deriv (resolventB μ) (x : ℂ) = ((B x - x) / (2 * x * (1 - B x)) : ℝ) := by
  have hd := ((analyticAt_resolventB μ (s := (x : ℂ)) (Or.inr hx.1)).differentiableAt.hasDerivAt).comp_ofReal
  have hr := (hasDerivAt_B hx).ofReal_comp
  apply hd.unique
  apply hr.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact he y ⟨hy.1, hy.2.le⟩

theorem deriv_resolventB_ode (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0)
    (he : ∀ x : ℝ, x ∈ Ioc 0 1 → resolventB μ (x : ℂ) = (B x : ℂ))
    {s : ℂ} (hs : 0 < s.re) :
    deriv (resolventB μ) s = -(s⁻¹ + resolventR μ s) / 2 := by
  have ha : AnalyticOnNhd ℂ (resolventB μ) {z : ℂ | 0 < z.re} :=
    fun z hz => analyticAt_resolventB μ (Or.inr hz)
  apply analytic_eqOn_rightHalfPlane_of_real_interval ha.deriv
    (fun z hz => ((analyticAt_id.inv (by intro h; change z = 0 at h; simp [h] at hz)).add
      (analyticAt_resolventR μ hμ (Or.inr hz))).neg.div_const) ?_ hs
  intro x hx
  change deriv (resolventB μ) (x : ℂ) = -((x : ℂ)⁻¹ + resolventR μ (x : ℂ)) / 2
  rw [deriv_resolventB_on_original μ he hx]
  have hz : (x : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
  have hz1 : (x : ℂ) - 1 ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hx.2.ne
  have hg : compactIntegral μ (x : ℂ) ≠ 0 := by
    intro h
    have hp := compactIntegral_real_pos μ hμ hx.1
    simp [h] at hp
  have hB := he x ⟨hx.1, hx.2.le⟩
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_one]
  rw [← hB, resolventB, resolventR]
  have heq : (1 : ℂ) - (1 - ((x : ℂ) - 1) * compactIntegral μ (x : ℂ)) =
      ((x : ℂ) - 1) * compactIntegral μ (x : ℂ) := by ring
  rw [heq]
  field_simp [hz, hz1, hg]
  ring

theorem hasDerivAt_resolventB_one (μ : FiniteMeasure Angle) :
    HasDerivAt (resolventB μ) (-compactIntegral μ 1) 1 := by
  have hd := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub
    (((hasDerivAt_id (1 : ℂ)).sub_const 1).mul
      ((analyticAt_compactIntegral μ (s := (1 : ℂ)) (Or.inr (by norm_num))).differentiableAt.hasDerivAt))
  convert! hd using 1
  simp only [id_eq, one_mul, sub_self, zero_mul, add_zero, zero_sub]

theorem compactIntegral_one (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0)
    (he : ∀ x : ℝ, x ∈ Ioc 0 1 → resolventB μ (x : ℂ) = (B x : ℂ)) :
    compactIntegral μ 1 = 1 := by
  have hp := compactIntegral_real_pos μ hμ (x := 1) (by norm_num)
  norm_num only [Complex.ofReal_one] at hp
  have hg : compactIntegral μ 1 ≠ 0 := by intro h; simp [h] at hp
  have hr := deriv_resolventB_ode μ hμ he (s := 1) (by norm_num)
  rw [(hasDerivAt_resolventB_one μ).deriv, resolventR] at hr
  simp only [one_mul, inv_one] at hr
  have hquad : 2 * compactIntegral μ 1 ^ 2 - compactIntegral μ 1 - 1 = 0 := by
    field_simp [hg] at hr
    linear_combination -hr
  have hf : (compactIntegral μ 1 - 1) * (2 * compactIntegral μ 1 + 1) = 0 := by
    linear_combination hquad
  rcases mul_eq_zero.mp hf with h | h
  · exact sub_eq_zero.mp h
  · have hh := congrArg Complex.re h
    norm_num at hh
    linarith

theorem resolventB_real (μ : FiniteMeasure Angle) (x : ℝ) : (resolventB μ (x : ℂ)).im = 0 := by
  rw [resolventB, compactIntegral_real]
  simp

theorem hasDerivAt_real_resolventB (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0)
    (he : ∀ x : ℝ, x ∈ Ioc 0 1 → resolventB μ (x : ℂ) = (B x : ℂ))
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => (resolventB μ (t : ℂ)).re)
      (-(x⁻¹ + (resolventR μ (x : ℂ)).re) / 2) x := by
  have hd := (analyticAt_resolventB μ (s := (x : ℂ)) (Or.inr hx)).differentiableAt.hasDerivAt
  rw [deriv_resolventB_ode μ hμ he hx] at hd
  convert! hd.real_of_complex using 1
  simp

theorem strictAntiOn_real_resolventB (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0)
    (he : ∀ x : ℝ, x ∈ Ioc 0 1 → resolventB μ (x : ℂ) = (B x : ℂ)) :
    StrictAntiOn (fun t : ℝ => (resolventB μ (t : ℂ)).re) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
  · intro x hx
    exact (hasDerivAt_real_resolventB μ hμ he hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi, mem_Ioi] at hx
    rw [(hasDerivAt_real_resolventB μ hμ he hx).deriv]
    have hp := resolventR_real_pos μ hμ hx
    have hi : 0 < x⁻¹ := inv_pos.mpr hx
    linarith

theorem exists_analytic_stieltjes_B : ∃ Be : ℂ → ℂ,
    AnalyticOnNhd ℂ Be {s : ℂ | 0 < s.im ∨ 0 < s.re} ∧
    (∀ x : ℝ, x ∈ Ioc 0 1 → Be (x : ℂ) = (B x : ℂ)) ∧
    (∀ x : ℝ, 0 < x → (Be (x : ℂ)).im = 0) ∧
    Be 1 = 1 ∧ deriv Be 1 = -1 ∧
    StrictAntiOn (fun x : ℝ => (Be (x : ℂ)).re) (Ioi 0) ∧
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ν : FiniteMeasure Angle,
      ∀ x : ℝ, 0 < x →
        -deriv (fun t : ℝ => (Be (t : ℂ)).re) x =
          (x⁻¹ + c + ∫ θ : Angle, (1 + (x - 1) * boundaryParameter θ)⁻¹ ∂(ν : Measure Angle)) / 2 := by
  obtain ⟨μ, hμ, hb⟩ := exists_B_resolvent
  have he (x : ℝ) (hx : x ∈ Ioc 0 1) : resolventB μ (x : ℂ) = (B x : ℂ) :=
    (hb (x : ℂ) (Or.inr ⟨Complex.ofReal_im x, hx.1⟩)).symm.trans (boundaryB_eq_B hx)
  obtain ⟨c, hc, ν, hν⟩ := resolventR_stieltjes μ hμ
  refine ⟨resolventB μ, fun s hs => analyticAt_resolventB μ hs, he,
    fun x _ => resolventB_real μ x, ?_, ?_, strictAntiOn_real_resolventB μ hμ he,
    c, hc, ν, ?_⟩
  · simp [resolventB]
  · rw [(hasDerivAt_resolventB_one μ).deriv, compactIntegral_one μ hμ he]
  · intro x hx
    rw [(hasDerivAt_real_resolventB μ hμ he hx).deriv, hν x hx]
    ring

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace EntropyPhotonNumber

section
open DiagonalForms.System MeasureTheory Set Filter Topology

theorem logarithmicMean_exp_pair {m : ℝ} (hm : 0 < m) (x : ℝ) :
    logMean (m*f x*Real.exp x) (m*f x*Real.exp (-x)) = m := by
  by_cases hx : x = 0
  · simp [hx, logMean]
  have hx2 : 2*x ≠ 0 := mul_ne_zero (by norm_num) hx
  have hmf : 0 < m*f x := mul_pos hm (f_pos x)
  have he : m*f x*Real.exp x ≠ m*f x*Real.exp (-x) := by
    intro h
    have ht := mul_left_cancel₀ hmf.ne' h
    have ht' := Real.exp_injective ht
    exact hx (by linarith)
  rw [logMean, ite_eq_right he, Real.log_mul hmf.ne' (Real.exp_ne_zero _),
    Real.log_mul hmf.ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_exp]
  have hn : m*f x*Real.exp (-x) - m*f x*Real.exp x = -2*m*x := by
    rw [mul_assoc, mul_assoc, f_mul_exp_neg, f_mul_exp]
    ring
  rw [hn]
  have hd : Real.log (m*f x) + -x - (Real.log (m*f x) + x) = -2*x := by ring
  rw [hd]
  field_simp

theorem dualLogarithmicMean_exp_pair {m : ℝ} (hm : 0 < m) (x : ℝ) :
    (m*f x*Real.exp x)*(m*f x*Real.exp (-x)) /
      logMean (m*f x*Real.exp x) (m*f x*Real.exp (-x)) = m * f x ^ 2 := by
  rw [logarithmicMean_exp_pair hm]
  have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  field_simp
  nlinarith [he]

theorem comparison_basic_weights {P I J : Type*} (D : DiagonalForms.System P I J)
    (m x y : P → ℝ) (hm : ∀ p, 0 < m p)
    (hxP : D.Comparison (fun p => m p*f (x p)*Real.exp (x p)))
    (hxM : D.Comparison (fun p => m p*f (x p)*Real.exp (-x p)))
    (hyP : D.Comparison (fun p => m p*f (y p)*Real.exp (y p)))
    (hyM : D.Comparison (fun p => m p*f (y p)*Real.exp (-y p))) :
    D.Comparison m ∧ D.Comparison (fun p => m p*f (x p)^2) ∧
      D.Comparison (fun p => m p*f (y p)^2) := by
  have hpos (t : P → ℝ) (p : P) : 0 < m p*f (t p)*Real.exp (t p) :=
    mul_pos (mul_pos (hm p) (f_pos _)) (Real.exp_pos _)
  have hneg (t : P → ℝ) (p : P) : 0 < m p*f (t p)*Real.exp (-t p) :=
    mul_pos (mul_pos (hm p) (f_pos _)) (Real.exp_pos _)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [logarithmicMean_exp_pair (hm _)] using
      D.comparison_logMean hxP hxM (hpos x) (hneg x)
  · simpa only [dualLogarithmicMean_exp_pair (hm _)] using
      D.comparison_dualLogMean hxP hxM (hpos x) (hneg x)
  · simpa only [dualLogarithmicMean_exp_pair (hm _)] using
      D.comparison_dualLogMean hyP hyM (hpos y) (hneg y)

theorem B_f_sq_all (x : ℝ) : B (f x ^ 2) = b x := by
  rcases le_total 0 x with hx | hx
  · exact B_f_sq hx
  · rw [← f_neg x, B_f_sq (neg_nonneg.mpr hx), b_neg]

def genericAdditionalE (D : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (∫ θ : UnitInterval, D ((1-θ.val)*s+θ.val*t))⁻¹

theorem genericAdditionalE_pos {D : ℝ → ℝ} (hc : ContinuousOn D (Ioi 0))
    (hp : ∀ q, 0 < q → 0 < D q) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    0 < genericAdditionalE D s t := by
  apply inv_pos.mpr
  have hct : Continuous (fun θ : UnitInterval => D ((1-θ.val)*s+θ.val*t)) :=
    hc.comp_continuous (by fun_prop) (affine_pos hs ht)
  have hsup : Function.support (fun θ : UnitInterval => D ((1-θ.val)*s+θ.val*t)) = univ := by
    ext θ
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hp _ (affine_pos hs ht θ)).ne'
  rw [integral_pos_iff_support_of_nonneg (fun θ => (hp _ (affine_pos hs ht θ)).le)
    (hct.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)), hsup,
    unitInterval_volume]
  norm_num

theorem genericAdditionalE_difference {B₀ D : ℝ → ℝ}
    (hc : ContinuousOn D (Ioi 0)) (hp : ∀ q, 0 < q → 0 < D q)
    (hd : ∀ q, 0 < q → HasDerivAt B₀ (-D q/2) q)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    2*genericAdditionalE D s t*(B₀ s-B₀ t) = t-s := by
  have hpos := genericAdditionalE_pos hc hp hs ht
  let q (θ : ℝ) := (1-θ)*s+θ*t
  have hqc : Continuous q := by dsimp [q]; fun_prop
  have hqp (θ : ℝ) (hθ : θ ∈ Icc 0 1) : 0 < q θ := affine_pos hs ht ⟨θ, hθ⟩
  have hI : IntervalIntegrable (fun θ => -D (q θ)/2*(t-s)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((hc.comp hqc.continuousOn hqp).neg.div_const 2).mul_const (t-s)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun θ => B₀ (q θ)) (f' := fun θ => -D (q θ)/2*(t-s)) (a := 0) (b := 1) (by
      intro θ hθ
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hθ
      have hq : HasDerivAt q (t-s) θ := by
        convert! (((hasDerivAt_const θ 1).sub (hasDerivAt_id θ)).mul_const s).add
          ((hasDerivAt_id θ).mul_const t) using 1
        ring
      exact (hd _ (hqp θ hθ)).comp θ hq) hI
  have hei : (∫ θ : UnitInterval, D (q θ.val)) = ∫ θ in (0 : ℝ)..1, D (q θ) :=
    by convert! integral_unitInterval (fun θ => D (q θ)) using 1
  have hnorm : (t-s)*(∫ θ : UnitInterval, D (q θ.val)) = 2*(B₀ s-B₀ t) := by
    rw [hei]
    have hq0 : q 0 = s := by simp [q]
    have hq1 : q 1 = t := by simp [q]
    rw [hq0, hq1] at hFTC
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div,
      intervalIntegral.integral_neg] at hFTC
    nlinarith
  have hn : (∫ θ : UnitInterval, D (q θ.val)) ≠ 0 := by
    exact (mt inv_eq_zero.mpr) (ne_of_gt hpos)
  dsimp [genericAdditionalE]
  calc
    2 * (∫ θ : UnitInterval, D ((1-θ.val)*s+θ.val*t))⁻¹ * (B₀ s-B₀ t) =
        (2*(B₀ s-B₀ t))*(∫ θ : UnitInterval, D (q θ.val))⁻¹ := by ring
    _ = t-s := by rw [← hnorm, mul_inv_cancel_right₀ hn]

theorem continuous_genericAdditionalE_f {D : ℝ → ℝ} (hc : ContinuousOn D (Ioi 0))
    (hp : ∀ q, 0 < q → 0 < D q) (x : ℝ) :
    Continuous (fun y => genericAdditionalE D (f x^2) (f y^2)) := by
  have hf : Continuous (fun z : ℝ × UnitInterval =>
      D ((1-z.2.val)*f x^2+z.2.val*f z.1^2)) := by
    have hv : Continuous (fun z : ℝ × UnitInterval => z.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact hc.comp_continuous
      (((continuous_const.sub hv).mul_const (f x^2)).add
        (hv.mul ((continuous_f.comp continuous_fst).pow 2)))
      (fun z => affine_pos (sq_pos_of_pos (f_pos x)) (sq_pos_of_pos (f_pos z.1)) z.2)
  have hi : Continuous (fun y => ∫ θ : UnitInterval,
      D ((1-θ.val)*f x^2+θ.val*f y^2)) := by
    simpa only [setIntegral_univ] using
      (continuous_parametric_integral_of_continuous (μ := volume) hf isCompact_univ)
  exact hi.inv₀ (fun y => (mt inv_eq_zero.mpr) (genericAdditionalE_pos hc hp
    (sq_pos_of_pos (f_pos x)) (sq_pos_of_pos (f_pos y))).ne')

theorem scalar_minimum_off {B₀ D : ℝ → ℝ}
    (hc : ContinuousOn D (Ioi 0)) (hp : ∀ q, 0 < q → 0 < D q)
    (hd : ∀ q, 0 < q → HasDerivAt B₀ (-D q/2) q)
    (hb : ∀ x, B₀ (f x^2) = b x) {x y : ℝ} (hxy : x+y ≠ 0) :
    (b x+b y-(x-y)^2/(b x+b y+2*genericAdditionalE D (f x^2) (f y^2)))/2 =
      f x*f y/f (x+y) := by
  let e := genericAdditionalE D (f x^2) (f y^2)
  have he : 0 < e := genericAdditionalE_pos hc hp
    (sq_pos_of_pos (f_pos x)) (sq_pos_of_pos (f_pos y))
  have hrel := genericAdditionalE_difference hc hp hd
    (sq_pos_of_pos (f_pos x)) (sq_pos_of_pos (f_pos y))
  rw [hb, hb] at hrel
  change 2*e*(b x-b y) = f y^2-f x^2 at hrel
  have hA : 0 < b x+b y+2*e := by positivity [b_pos x, b_pos y]
  have hr : (b x-b y)*(b x+b y+2*e) = (x-y)*(x+y) := by
    nlinarith [b_sq x, b_sq y]
  rw [target_eq_of_add_ne_zero hxy]
  change (b x+b y-(x-y)^2/(b x+b y+2*e))/2 = (y*b x+x*b y)/(x+y)
  field_simp
  nlinarith [congrArg (fun z : ℝ => z*(x-y)) hr]

theorem scalar_minimum {B₀ D : ℝ → ℝ}
    (hc : ContinuousOn D (Ioi 0)) (hp : ∀ q, 0 < q → 0 < D q)
    (hd : ∀ q, 0 < q → HasDerivAt B₀ (-D q/2) q)
    (hb : ∀ x, B₀ (f x^2) = b x) (x y : ℝ) :
    (b x+b y-(x-y)^2/(b x+b y+2*genericAdditionalE D (f x^2) (f y^2)))/2 =
      f x*f y/f (x+y) := by
  by_cases hxy : x+y ≠ 0
  · exact scalar_minimum_off hc hp hd hb hxy
  have hy : y = -x := by
    have hz := not_ne_iff.mp hxy
    linarith
  subst y
  let L (y : ℝ) :=
    (b x+b y-(x-y)^2/(b x+b y+2*genericAdditionalE D (f x^2) (f y^2)))/2
  let R (y : ℝ) := f x*f y/f (x+y)
  have hL : Continuous L := by
    have hden : ∀ y, b x+b y+2*genericAdditionalE D (f x^2) (f y^2) ≠ 0 := by
      intro y
      exact ne_of_gt (by positivity [b_pos x, b_pos y,
        genericAdditionalE_pos hc hp (sq_pos_of_pos (f_pos x)) (sq_pos_of_pos (f_pos y))])
    exact (((continuous_const.add continuous_b).sub
      ((continuous_const.sub continuous_id).pow 2 |>.div
        ((continuous_const.add continuous_b).add
          ((continuous_genericAdditionalE_f hc hp x).const_mul 2)) hden)).div_const 2)
  have hR : Continuous R :=
    (continuous_const.mul continuous_f).div
      (continuous_f.comp (continuous_const.add continuous_id)) (fun y => (f_pos (x+y)).ne')
  have heq : L =ᶠ[𝓝[≠] (-x)] R := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    apply scalar_minimum_off hc hp hd hb
    simp only [mem_compl_iff, mem_singleton_iff] at hy
    intro h
    exact hy (by linarith)
  exact tendsto_nhds_unique
    (hL.continuousAt.mono_left nhdsWithin_le_nhds)
    ((hR.continuousAt.mono_left nhdsWithin_le_nhds).congr' heq.symm)

def interpolationQuadratic (m x y e : ℝ) (ξ φ : ℂ) : ℝ :=
  1/4*(m*f x*Real.exp x*Complex.normSq (ξ-φ)) +
  1/4*(m*f x*Real.exp (-x)*Complex.normSq (ξ+φ)) +
  1/4*(m*f y*Real.exp y*Complex.normSq (ξ+φ)) +
  1/4*(m*f y*Real.exp (-y)*Complex.normSq (ξ-φ)) +
  m*e*Complex.normSq φ

theorem interpolationQuadratic_expand (m x y e : ℝ) (ξ φ : ℂ) :
    interpolationQuadratic m x y e ξ φ =
      m*(b x+b y)/2*Complex.normSq ξ +
      m*((b x+b y)/2+e)*Complex.normSq φ -
      m*(x-y)*(ξ.re*φ.re+ξ.im*φ.im) := by
  unfold interpolationQuadratic
  have hp (z : ℝ) : m*f z*Real.exp z = m*(b z+z) := by
    rw [mul_assoc, f_mul_exp]
  have hn (z : ℝ) : m*f z*Real.exp (-z) = m*(b z-z) := by
    rw [mul_assoc, f_mul_exp_neg]
  rw [hp, hp, hn, hn]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im]
  ring

theorem interpolationQuadratic_complete {m x y e : ℝ} (he : 0 < e)
    (ξ φ : ℂ) :
    interpolationQuadratic m x y e ξ φ =
      m*((b x+b y-(x-y)^2/(b x+b y+2*e))/2)*Complex.normSq ξ +
      m*(b x+b y+2*e)/2 *
        Complex.normSq (φ-(((x-y)/(b x+b y+2*e) : ℝ) : ℂ)*ξ) := by
  have hA : b x+b y+2*e ≠ 0 := ne_of_gt (by positivity [b_pos x, b_pos y])
  rw [interpolationQuadratic_expand]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  field_simp
  ring

theorem interpolationQuadratic_lower {B₀ D : ℝ → ℝ}
    (hc : ContinuousOn D (Ioi 0)) (hp : ∀ q, 0 < q → 0 < D q)
    (hd : ∀ q, 0 < q → HasDerivAt B₀ (-D q/2) q)
    (hb : ∀ x, B₀ (f x^2) = b x) {m : ℝ} (hm : 0 < m) (x y : ℝ) (ξ φ : ℂ) :
    fourWeightTarget m x y * Complex.normSq ξ ≤
      interpolationQuadratic m x y (genericAdditionalE D (f x^2) (f y^2)) ξ φ := by
  have he := genericAdditionalE_pos hc hp (sq_pos_of_pos (f_pos x)) (sq_pos_of_pos (f_pos y))
  rw [interpolationQuadratic_complete he, scalar_minimum hc hp hd hb]
  have hnon : 0 ≤ m*(b x+b y+2*genericAdditionalE D (f x^2) (f y^2))/2 *
      Complex.normSq (φ-(((x-y)/(b x+b y+2*genericAdditionalE D (f x^2) (f y^2)) : ℝ) : ℂ)*ξ) := by
    exact mul_nonneg (div_nonneg (mul_nonneg hm.le (by positivity [b_pos x, b_pos y])) (by norm_num))
      (Complex.normSq_nonneg _)
  dsimp [fourWeightTarget]
  convert le_add_of_nonneg_right hnon using 1
  ring

theorem interpolationQuadratic_minimum {B₀ D : ℝ → ℝ}
    (hc : ContinuousOn D (Ioi 0)) (hp : ∀ q, 0 < q → 0 < D q)
    (hd : ∀ q, 0 < q → HasDerivAt B₀ (-D q/2) q)
    (hb : ∀ x, B₀ (f x^2) = b x) {m : ℝ} (x y : ℝ) (ξ : ℂ) :
    interpolationQuadratic m x y (genericAdditionalE D (f x^2) (f y^2)) ξ
      ((((x-y)/(b x+b y+2*genericAdditionalE D (f x^2) (f y^2)) : ℝ) : ℂ)*ξ) =
      fourWeightTarget m x y * Complex.normSq ξ := by
  have he := genericAdditionalE_pos hc hp (sq_pos_of_pos (f_pos x)) (sq_pos_of_pos (f_pos y))
  rw [interpolationQuadratic_complete he, scalar_minimum hc hp hd hb]
  simp only [sub_self, map_zero, mul_zero, add_zero]
  dsimp [fourWeightTarget]
  ring

theorem comparison_interpolation_of_stieltjes {P I J : Type*} (S : DiagonalForms.System P I J)
    {B₀ D : ℝ → ℝ} (hc : ContinuousOn D (Ioi 0)) (hp : ∀ q, 0 < q → 0 < D q)
    (hd : ∀ q, 0 < q → HasDerivAt B₀ (-D q/2) q) (hb : ∀ x, B₀ (f x^2) = b x)
    (m x y : P → ℝ) (hm : ∀ p, 0 < m p)
    (hxP : S.Comparison (fun p => m p*f (x p)*Real.exp (x p)))
    (hxM : S.Comparison (fun p => m p*f (x p)*Real.exp (-x p)))
    (hyP : S.Comparison (fun p => m p*f (y p)*Real.exp (y p)))
    (hyM : S.Comparison (fun p => m p*f (y p)*Real.exp (-y p)))
    (hE : S.Comparison (fun p => m p*genericAdditionalE D (f (x p)^2) (f (y p)^2))) :
    S.Comparison (fun p => fourWeightTarget (m p) (x p) (y p)) := by
  apply S.comparison_fiveQuadratic
    (δ := fun p => (x p-y p)/(b (x p)+b (y p)+2*genericAdditionalE D (f (x p)^2) (f (y p)^2)))
    (S.comparison_smul hxP (by norm_num : (0 : ℝ) ≤ 1/4))
    (S.comparison_smul hxM (by norm_num : (0 : ℝ) ≤ 1/4))
    (S.comparison_smul hyP (by norm_num : (0 : ℝ) ≤ 1/4))
    (S.comparison_smul hyM (by norm_num : (0 : ℝ) ≤ 1/4)) hE
  · intro p ξ
    convert interpolationQuadratic_minimum hc hp hd hb (x p) (y p) ξ using 1
    dsimp [fiveQuadratic, interpolationQuadratic]
    ring
  · intro p ξ φ
    convert interpolationQuadratic_lower hc hp hd hb (hm p) (x p) (y p) ξ φ using 1
    dsimp [fiveQuadratic, interpolationQuadratic]
    ring

end

open DiagonalForms.System MeasureTheory Set Filter Topology Herglotz

theorem four_weight_interpolation {P I J : Type*} (S : DiagonalForms.System P I J)
    (m x y : P → ℝ) (hm : ∀ p, 0 < m p)
    (hxP : S.Comparison (fun p => m p*f (x p)*Real.exp (x p)))
    (hxM : S.Comparison (fun p => m p*f (x p)*Real.exp (-x p)))
    (hyP : S.Comparison (fun p => m p*f (y p)*Real.exp (y p)))
    (hyM : S.Comparison (fun p => m p*f (y p)*Real.exp (-y p))) :
    S.Comparison (fun p => fourWeightTarget (m p) (x p) (y p)) := by
  obtain ⟨μ, hμ, hμB⟩ := exists_B_resolvent
  have he (q : ℝ) (hq : q ∈ Ioc 0 1) : resolventB μ (q : ℂ) = (B q : ℂ) :=
    (hμB (q : ℂ) (Or.inr ⟨Complex.ofReal_im q, hq.1⟩)).symm.trans (boundaryB_eq_B hq)
  obtain ⟨c, hc, ν, hν⟩ := resolventR_stieltjes μ hμ
  let D := resolventWeight (ν : Measure Angle) c boundaryParameter
  let B₀ := fun q : ℝ => (resolventB μ (q : ℂ)).re
  have hcont : ContinuousOn D (Ioi 0) :=
    continuousOn_resolventWeight (ν : Measure Angle) continuous_boundaryParameter boundaryParameter_mem
  have hpos (q : ℝ) (hq : 0 < q) : 0 < D q :=
    resolventWeight_pos (ν : Measure Angle) hc boundaryParameter_mem hq
  have hd (q : ℝ) (hq : 0 < q) : HasDerivAt B₀ (-D q/2) q := by
    have h := hasDerivAt_real_resolventB μ hμ he hq
    rw [hν q hq] at h
    convert h using 1
    dsimp [D, B₀, resolventWeight]
    ring
  have hb (z : ℝ) : B₀ (f z^2) = b z := by
    have hq : f z^2 ∈ Ioc (0 : ℝ) 1 :=
      ⟨sq_pos_of_pos (f_pos z), by nlinarith [f_pos z, f_le_one z]⟩
    dsimp [B₀]
    rw [he _ hq, Complex.ofReal_re, B_f_sq_all]
  obtain ⟨hmc, hsc, htc⟩ := comparison_basic_weights S m x y hm hxP hxM hyP hyM
  have hE : S.Comparison (fun p => m p*genericAdditionalE D (f (x p)^2) (f (y p)^2)) := by
    have h := S.comparison_resolvent_average (ν : Measure Angle) ⟨0, ⟨le_rfl, by positivity⟩⟩ hc
      continuous_boundaryParameter boundaryParameter_mem hm
      (fun p => sq_pos_of_pos (f_pos (x p))) (fun p => sq_pos_of_pos (f_pos (y p))) hmc hsc htc
    simpa only [D, genericAdditionalE, div_eq_mul_inv] using h
  exact comparison_interpolation_of_stieltjes S hcont hpos hd hb m x y hm hxP hxM hyP hyM hE

end EntropyPhotonNumber

end

end OAI
