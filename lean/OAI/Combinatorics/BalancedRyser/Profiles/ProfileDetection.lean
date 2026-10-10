import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.MeasureTheory.Topology
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

namespace OAI

open Filter
open scoped Topology

namespace Balanced.ProfileDetection

theorem tendsto_scaled_exponential_series
    {ι : Type*} {a ell : ι → ℝ} (ha : Summable (fun i => |a i|))
    (hell : Function.Injective ell) (m : ι)
    (hmin : ∀ i, a i ≠ 0 → ell m ≤ ell i) :
    Tendsto (fun t : ℝ => Real.exp (ell m * t) *
      ∑' i, a i * Real.exp (-ell i * t)) atTop (𝓝 (a m)) := by
  classical
  have hterm (i : ι) :
      Tendsto (fun t : ℝ => a i * Real.exp (-(ell i - ell m) * t))
        atTop (𝓝 (if i = m then a i else 0)) := by
    by_cases him : i = m
    · subst i
      simp
    · by_cases hai : a i = 0
      · simp [hai, him]
      · have hdiff : 0 < ell i - ell m := by
          exact sub_pos.mpr (lt_of_le_of_ne (hmin i hai) (fun h => him (hell h.symm)))
        have ht : Tendsto (fun t : ℝ => (ell i - ell m) * t) atTop atTop :=
          tendsto_id.const_mul_atTop hdiff
        have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul (a i)
        simpa only [ite_eq_right_iff.mpr (fun h => (him h).elim), Function.comp_apply,
          neg_mul, mul_zero] using he
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ i,
      ‖a i * Real.exp (-(ell i - ell m) * t)‖ ≤ |a i| := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht i
    by_cases hai : a i = 0
    · simp [hai]
    · have hd : 0 ≤ ell i - ell m := sub_nonneg.mpr (hmin i hai)
      have he : Real.exp (-(ell i - ell m) * t) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        nlinarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans_eq (mul_one _)
  have hsum := tendsto_tsum_of_dominated_convergence ha hterm hbound
  simp only [tsum_ite_eq] at hsum
  convert hsum using 1
  ext t
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  rw [← mul_assoc, mul_comm (Real.exp (ell m * t)) (a i), mul_assoc,
    ← Real.exp_add]
  congr 2
  ring

theorem summable_exponential_series
    {ι : Type*} {a ell : ι → ℝ} (ha : Summable (fun i => |a i|))
    (hell : ∀ i, 0 ≤ ell i) {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun i => a i * Real.exp (-ell i * t)) := by
  apply ha.of_norm_bounded
  intro i
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-ell i * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hell i)) ht)
  exact (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans_eq (mul_one _)

theorem analyticOnNhd_complex_exponential_series
    {ι : Type*} {a ell : ι → ℝ} (ha : Summable (fun i => |a i|))
    (hell : ∀ i, 0 ≤ ell i) :
    AnalyticOnNhd ℂ (fun z : ℂ =>
      ∑' i, (a i : ℂ) * Complex.exp (-(ell i : ℂ) * z))
      {z | 0 < z.re} := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hopen
  apply Complex.differentiableOn_tsum_of_summable_norm ha
  · intro i
    fun_prop
  · exact hopen
  · intro i z hz
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
    have he : Real.exp (-ell i * z.re) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hell i)) (le_of_lt hz))
    exact (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans_eq (mul_one _)

theorem analyticOnNhd_exponential_series
    {ι : Type*} {a ell : ι → ℝ} (ha : Summable (fun i => |a i|))
    (hell : ∀ i, 0 ≤ ell i) :
    AnalyticOnNhd ℝ (fun t : ℝ => ∑' i, a i * Real.exp (-ell i * t))
      (Set.Ioi 0) := by
  let F : ℂ → ℂ := fun z =>
    ∑' i, (a i : ℂ) * Complex.exp (-(ell i : ℂ) * z)
  have heq (t : ℝ) : F (t : ℂ) =
      ((∑' i, a i * Real.exp (-ell i * t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro i
    simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
  intro t ht
  have hF : AnalyticAt ℂ F (t : ℂ) :=
    analyticOnNhd_complex_exponential_series ha hell (t : ℂ) ht
  have hinner : AnalyticAt ℝ (fun x : ℝ => F (x : ℂ)) t :=
    hF.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
  have hcomp := (Complex.reCLM.analyticAt (F (t : ℂ))).comp
    (f := fun x : ℝ => F (x : ℂ)) hinner
  apply hcomp.congr
  filter_upwards [] with x
  change (F (x : ℂ)).re = _
  rw [heq, Complex.ofReal_re]

theorem exists_least_supported_exponent
    {ι : Type*} {a ell : ι → ℝ}
    (hfinite : ∀ R : ℝ, {i | ell i ≤ R}.Finite)
    (hne : ∃ i, a i ≠ 0) :
    ∃ m, a m ≠ 0 ∧ ∀ i, a i ≠ 0 → ell m ≤ ell i := by
  classical
  obtain ⟨i₀, hi₀⟩ := hne
  let s : Set ι := {i | a i ≠ 0 ∧ ell i ≤ ell i₀}
  have hs : s.Finite := (hfinite (ell i₀)).subset (fun _ h => h.2)
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image s ell hs ⟨i₀, hi₀, le_rfl⟩
  refine ⟨m, hm.1, fun i hai => ?_⟩
  by_cases hi : ell i ≤ ell i₀
  · exact hmin i ⟨hai, hi⟩
  · exact hm.2.trans (le_of_lt (lt_of_not_ge hi))

theorem coefficients_zero_of_exponential_series_eventually_zero
    {ι : Type*} {a ell : ι → ℝ} (ha : Summable (fun i => |a i|))
    (hell : Function.Injective ell)
    (hfinite : ∀ R : ℝ, {i | ell i ≤ R}.Finite)
    (hzero : ∀ᶠ t : ℝ in atTop,
      (∑' i, a i * Real.exp (-ell i * t)) = 0) :
    ∀ i, a i = 0 := by
  classical
  by_contra h
  obtain ⟨m, hm, hmin⟩ := exists_least_supported_exponent hfinite (by simpa using h)
  have hlim := tendsto_scaled_exponential_series ha hell m hmin
  have hlim0 : Tendsto (fun t : ℝ => Real.exp (ell m * t) *
      ∑' i, a i * Real.exp (-ell i * t)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hzero] with t ht
    rw [ht, mul_zero]
  exact hm (tendsto_nhds_unique hlim hlim0)

theorem exists_positive_exponential_series_ne_zero
    {ι : Type*} {a ell : ι → ℝ} (ha : Summable (fun i => |a i|))
    (hell : Function.Injective ell)
    (hfinite : ∀ R : ℝ, {i | ell i ≤ R}.Finite)
    (hne : ∃ i, a i ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ (∑' i, a i * Real.exp (-ell i * t)) ≠ 0 := by
  by_contra h
  push Not at h
  have hzero : ∀ᶠ t : ℝ in atTop,
      (∑' i, a i * Real.exp (-ell i * t)) = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact h t ht
  obtain ⟨i, hi⟩ := hne
  exact hi (coefficients_zero_of_exponential_series_eventually_zero ha hell hfinite hzero i)

theorem exponential_series_ae_ne_zero
    {ι : Type*} {a ell : ι → ℝ} (ha : Summable (fun i => |a i|))
    (hell : Function.Injective ell) (hnonneg : ∀ i, 0 ≤ ell i)
    (hfinite : ∀ R : ℝ, {i | ell i ≤ R}.Finite)
    (hne : ∃ i, a i ≠ 0) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∑' i, a i * Real.exp (-ell i * t)) ≠ 0 := by
  obtain ⟨t, ht, hval⟩ := exists_positive_exponential_series_ne_zero ha hell hfinite hne
  have hd := (analyticOnNhd_exponential_series ha hnonneg).preimage_zero_mem_codiscreteWithin hval ht isConnected_Ioi
  exact ae_restrict_le_codiscreteWithin measurableSet_Ioi hd

theorem analyticOnNhd_log_exponential_series
    {ι : Type*} {a ell : ι → ℝ} (ha : Summable (fun i => |a i|))
    (hell : ∀ i, 0 ≤ ell i) :
    AnalyticOnNhd ℝ (fun z : ℝ => ∑' i, a i * Real.exp (ell i * Real.log z))
      (Set.Ioo 0 1) := by
  intro z hz
  have hlog : 0 < -Real.log z := neg_pos.mpr (Real.log_neg hz.1 hz.2)
  have hA := analyticOnNhd_exponential_series ha hell (-Real.log z) hlog
  have hc := hA.comp (f := fun x : ℝ => -Real.log x) (analyticAt_log hz.1).neg
  apply hc.congr
  filter_upwards [] with x
  simp only [Function.comp_apply]
  apply tsum_congr
  intro i
  congr 2
  ring

theorem log_exponential_series_ae_ne_zero
    {ι : Type*} {a ell : ι → ℝ} (ha : Summable (fun i => |a i|))
    (hell : Function.Injective ell) (hnonneg : ∀ i, 0 ≤ ell i)
    (hfinite : ∀ R : ℝ, {i | ell i ≤ R}.Finite)
    (hne : ∃ i, a i ≠ 0) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)),
      (∑' i, a i * Real.exp (ell i * Real.log z)) ≠ 0 := by
  obtain ⟨t, ht, hval⟩ := exists_positive_exponential_series_ne_zero ha hell hfinite hne
  have hz : Real.exp (-t) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)⟩
  have hval' : (∑' i, a i * Real.exp (ell i * Real.log (Real.exp (-t)))) ≠ 0 := by
    simpa only [Real.log_exp, mul_neg, neg_mul] using hval
  have hd := (analyticOnNhd_log_exponential_series ha hnonneg).preimage_zero_mem_codiscreteWithin hval' hz (isConnected_Ioo (by norm_num))
  exact ae_restrict_le_codiscreteWithin measurableSet_Ioo hd

noncomputable def profileExponent (n : ℕ × ℕ) : ℝ :=
  n.1 + Real.sqrt 2 * n.2

theorem profileExponent_injective : Function.Injective profileExponent := by
  intro m n h
  have hsecond : m.2 = n.2 := by
    by_contra hne
    have hrat : (m.2 : ℚ) - (n.2 : ℚ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hne)
    apply (irrational_sqrt_two.mul_ratCast hrat).ne_rat
      ((n.1 : ℚ) - (m.1 : ℚ))
    push_cast
    dsimp [profileExponent] at h
    nlinarith
  apply Prod.ext
  · have heq : (m.1 : ℝ) = (n.1 : ℝ) := by
      dsimp [profileExponent] at h
      rw [hsecond] at h
      linarith
    exact_mod_cast heq
  · exact hsecond

theorem profileExponent_finite_sublevel (R : ℝ) :
    {n | profileExponent n ≤ R}.Finite := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  apply ((Set.finite_Iic (Nat.ceil R)).prod (Set.finite_Iic (Nat.ceil R))).subset
  intro n hn
  change n.1 ≤ Nat.ceil R ∧ n.2 ≤ Nat.ceil R
  have hi : (n.1 : ℝ) ≤ R := by
    dsimp [profileExponent] at hn
    nlinarith [(Nat.cast_nonneg n.2 : (0 : ℝ) ≤ n.2)]
  have hj : (n.2 : ℝ) ≤ R := by
    dsimp [profileExponent] at hn
    nlinarith [(Nat.cast_nonneg n.1 : (0 : ℝ) ≤ n.1), (Nat.cast_nonneg n.2 : (0 : ℝ) ≤ n.2)]
  constructor
  · exact_mod_cast hi.trans (Nat.le_ceil R)
  · exact_mod_cast hj.trans (Nat.le_ceil R)

theorem profileExponent_nonneg (n : ℕ × ℕ) : 0 ≤ profileExponent n := by
  unfold profileExponent
  positivity

theorem profile_power_series_ae_ne_zero
    {a : ℕ × ℕ → ℝ} (ha : Summable (fun n => |a n|))
    (hne : ∃ n, a n ≠ 0) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)),
      (∑' n, a n * z ^ (profileExponent n)) ≠ 0 := by
  have h := log_exponential_series_ae_ne_zero ha profileExponent_injective
    profileExponent_nonneg profileExponent_finite_sublevel hne
  filter_upwards [h, MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz hzone
  convert hz using 1
  apply tsum_congr
  intro n
  rw [Real.rpow_def_of_pos hzone.1, mul_comm (Real.log z)]

theorem summable_profile_power_series
    {a : ℕ × ℕ → ℝ} (ha : Summable (fun n => |a n|))
    {z : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) 1) :
    Summable (fun n => a n * z ^ (profileExponent n)) := by
  apply ha.of_norm_bounded
  intro n
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hz.1.le _)]
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_one hz.1.le hz.2.le (profileExponent_nonneg n))
    (abs_nonneg _)).trans_eq (mul_one _)

theorem profile_power_series_ae_ne_of_ne
    {a b : ℕ × ℕ → ℝ} (ha : Summable (fun n => |a n|))
    (hb : Summable (fun n => |b n|)) (hne : a ≠ b) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)),
      (∑' n, a n * z ^ (profileExponent n)) ≠
      (∑' n, b n * z ^ (profileExponent n)) := by
  have hd : Summable (fun n => |a n - b n|) := (ha.of_abs.sub hb.of_abs).abs
  have hne' : ∃ n, a n - b n ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    funext n
    exact sub_eq_zero.mp (h n)
  have h := profile_power_series_ae_ne_zero hd hne'
  filter_upwards [h, MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz hzone
  have heq : (∑' n, (a n - b n) * z ^ (profileExponent n)) =
      (∑' n, a n * z ^ (profileExponent n)) -
      (∑' n, b n * z ^ (profileExponent n)) := by
    simp_rw [sub_mul]
    exact (summable_profile_power_series ha hzone).tsum_sub
      (summable_profile_power_series hb hzone)
  rw [heq] at hz
  exact sub_ne_zero.mp hz

theorem profile_coefficients_zero_of_eventually_zero
    {a : ℕ × ℕ → ℝ} (ha : Summable (fun n => |a n|))
    (hzero : ∀ᶠ t : ℝ in atTop,
      (∑' n, a n * Real.exp (-profileExponent n * t)) = 0) :
    ∀ n, a n = 0 :=
  coefficients_zero_of_exponential_series_eventually_zero ha
    profileExponent_injective profileExponent_finite_sublevel hzero

end Balanced.ProfileDetection

end OAI
