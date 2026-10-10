import Mathlib

namespace OAI

open scoped BigOperators
open Finset

/-! Exact analytic kernels of §04, necessary for the simplex minimization.
Only the point values of integrands at zero are irrelevant to the integrals. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace KServer.SimplexAnalytic

def regularF (h y : ℝ) : ℝ := (h + y)^2 / h

def markedF (u H y : ℝ) : ℝ := u + H * y * (1 + y)

def kernel (F : ℝ → ℝ) (s : ℝ) : ℝ := 1 / F (Real.log (1 / s))

def singularKernel (F : ℝ → ℝ) (s : ℝ) : ℝ := kernel F s / s

def primitive (F : ℝ → ℝ) (Cα ell η S B base a : ℝ) : ℝ :=
  Cα * ell * ∫ s in base..a, (S - (1 + η) * B / s) / F (Real.log (1 / s))

/-- Continuous primitive of the regular B/s term, including the improper endpoint. -/
def regularTail (h : ℝ) : ℝ → ℝ := Function.update (fun s => h / (h - Real.log s)) 0 0

lemma regularTail_zero (h : ℝ) : regularTail h 0 = 0 := by simp [regularTail]

lemma regularTail_of_ne {s : ℝ} (hs : s ≠ 0) (h : ℝ) :
    regularTail h s = h / (h - Real.log s) := by simp [regularTail, Function.update_of_ne hs]

lemma regularTail_continuousAt_zero (h : ℝ) : ContinuousAt (regularTail h) 0 := by
  apply continuousAt_update_same.mpr
  have ht : Tendsto (fun s : ℝ => h - Real.log s) (𝓝[≠] 0) atTop := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      tendsto_atTop_add_const_left (𝓝[≠] (0 : ℝ)) h
        (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsNE_zero)
  exact tendsto_const_nhds.div_atTop ht

lemma regularTail_derivative {h s : ℝ} (hh : 0 < h) (hs : s ∈ Set.Ioc 0 1) :
    HasDerivAt (regularTail h) (h / (s * (h - Real.log s)^2)) s := by
  have hlog : Real.log s ≤ 0 := Real.log_nonpos hs.1.le hs.2
  have hn : h - Real.log s ≠ 0 := by linarith
  have hd := (hasDerivAt_const s h).div
    ((hasDerivAt_const s h).sub (Real.hasDerivAt_log hs.1.ne')) hn
  have heq : (0 * (h - Real.log s) - h * (0 - s⁻¹)) / (h - Real.log s)^2 =
      h / (s * (h - Real.log s)^2) := by
    field_simp
    ring
  dsimp at hd
  rw [heq] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hs.1.ne'] with x hx
  exact regularTail_of_ne hx h

lemma regularTail_continuousOn {h : ℝ} (hh : 0 < h) :
    ContinuousOn (regularTail h) (Set.Icc 0 1) := by
  intro s hs
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · subst s
    exact (regularTail_continuousAt_zero h).continuousWithinAt
  · exact (regularTail_derivative hh ⟨h0, hs.2⟩).continuousAt.continuousWithinAt

lemma regular_singular_formula {h s : ℝ} :
    singularKernel (regularF h) s = h / (s * (h - Real.log s)^2) := by
  dsimp [singularKernel, kernel, regularF]
  have he : Real.log (1 / s) = -Real.log s := by rw [one_div, Real.log_inv]
  rw [he]
  simp only [← sub_eq_add_neg, div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
  ring

lemma regular_singular_intervalIntegrable {h : ℝ} (hh : 0 < h) :
    IntervalIntegrable (singularKernel (regularF h)) volume 0 1 := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    (g := regularTail h)
  · simpa using regularTail_continuousOn hh
  · intro s hs
    simp only [min_eq_left (show (0 : ℝ) ≤ 1 by norm_num),
      max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    rw [regular_singular_formula]
    exact regularTail_derivative hh ⟨hs.1, hs.2.le⟩
  · intro s hs
    simp only [min_eq_left (show (0 : ℝ) ≤ 1 by norm_num),
      max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    rw [regular_singular_formula]
    exact div_nonneg hh.le (mul_nonneg hs.1.le (sq_nonneg _))

lemma regular_singular_integral {h : ℝ} (hh : 0 < h) :
    ∫ s in (0 : ℝ)..1, singularKernel (regularF h) s = 1 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show (0 : ℝ) ≤ 1 by norm_num)
    (regularTail_continuousOn hh)
    (fun s (hs : s ∈ Set.Ioo 0 1) => by
      rw [regular_singular_formula]
      exact regularTail_derivative hh ⟨hs.1, hs.2.le⟩)
    (regular_singular_intervalIntegrable hh)
  simpa [regularTail, hh.ne'] using he

lemma kernel_measurable {F : ℝ → ℝ} (hF : Measurable F) : Measurable (kernel F) := by
  unfold kernel
  fun_prop

lemma singularKernel_measurable {F : ℝ → ℝ} (hF : Measurable F) :
    Measurable (singularKernel F) :=
  (kernel_measurable hF).div measurable_id

lemma log_inverse_nonneg {s : ℝ} (hs : s ∈ Set.Ioc 0 1) : 0 ≤ Real.log (1 / s) := by
  rw [one_div, Real.log_inv]
  exact neg_nonneg.mpr (Real.log_nonpos hs.1.le hs.2)

lemma marked_quadratic_lower {u H c y : ℝ} (hy : 0 ≤ y) (hc : 0 < c)
    (hcu : c ≤ u) (hcH : 2 * c ≤ H) : c * (1 + y)^2 ≤ markedF u H y := by
  unfold markedF
  nlinarith [mul_nonneg (sub_nonneg.mpr hcH) (mul_nonneg hy (show 0 ≤ 1 + y by linarith)),
    mul_nonneg hc.le (sq_nonneg y)]

lemma singular_dominated {F : ℝ → ℝ} {c s : ℝ} (hc : 0 < c)
    (hF : ∀ y, 0 ≤ y → c * (1 + y)^2 ≤ F y) (hs : s ∈ Set.Ioc 0 1) :
    0 ≤ singularKernel F s ∧
      singularKernel F s ≤ (1 / c) * singularKernel (regularF 1) s := by
  have hy := log_inverse_nonneg hs
  have hp : 0 < c * (1 + Real.log (1 / s))^2 := by positivity
  have hden : 0 < F (Real.log (1 / s)) := hp.trans_le (hF _ hy)
  constructor
  · exact div_nonneg (div_nonneg (by norm_num) hden.le) hs.1.le
  · have hi := one_div_le_one_div_of_le hp (hF _ hy)
    have he : (1 / (c * (1 + Real.log (1 / s))^2)) / s =
        (1 / c) * singularKernel (regularF 1) s := by
      dsimp [singularKernel, kernel, regularF]
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    rw [← he]
    exact div_le_div_of_nonneg_right hi hs.1.le

lemma singular_intervalIntegrable_of_quadratic {F : ℝ → ℝ} {c : ℝ}
    (hFm : Measurable F) (hc : 0 < c)
    (hF : ∀ y, 0 ≤ y → c * (1 + y)^2 ≤ F y) :
    IntervalIntegrable (singularKernel F) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have hreg := ((intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show (0 : ℝ) ≤ 1 by norm_num)).mp (regular_singular_intervalIntegrable (by norm_num : (0 : ℝ) < 1))).const_mul (1 / c)
  apply hreg.mono' (singularKernel_measurable hFm).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (singular_dominated hc hF hs).1]
  exact (singular_dominated hc hF hs).2

lemma kernel_intervalIntegrable {F : ℝ → ℝ} (hFm : Measurable F)
    (hF : ∀ y, 0 ≤ y → 0 < F y)
    (hint : IntervalIntegrable (singularKernel F) volume 0 1) :
    IntervalIntegrable (kernel F) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show (0 : ℝ) ≤ 1 by norm_num)).mp hint
  apply hi.mono' (kernel_measurable hFm).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hk : 0 ≤ kernel F s := div_nonneg (by norm_num) (hF _ (log_inverse_nonneg hs)).le
  rw [Real.norm_eq_abs, abs_of_nonneg hk]
  apply (le_div_iff₀ hs.1).mpr
  exact mul_le_of_le_one_right hk hs.2

lemma integrand_affine (F : ℝ → ℝ) (η S B s : ℝ) :
    (S - (1 + η) * B / s) / F (Real.log (1 / s)) =
      S * kernel F s - (1 + η) * B * singularKernel F s := by
  dsimp [kernel, singularKernel]
  ring

lemma integrand_intervalIntegrable {F : ℝ → ℝ} (hFm : Measurable F)
    (hF : ∀ y, 0 ≤ y → 0 < F y)
    (hint : IntervalIntegrable (singularKernel F) volume 0 1) (η S B : ℝ) :
    IntervalIntegrable (fun s => (S - (1 + η) * B / s) / F (Real.log (1 / s))) volume 0 1 := by
  simp_rw [integrand_affine]
  exact ((kernel_intervalIntegrable hFm hF hint).const_mul S).sub
    (hint.const_mul ((1 + η) * B))

lemma primitive_continuousOn {F : ℝ → ℝ} (hFm : Measurable F)
    (hF : ∀ y, 0 ≤ y → 0 < F y)
    (hint : IntervalIntegrable (singularKernel F) volume 0 1)
    (Cα ell η S B : ℝ) {base : ℝ} (hb : base ∈ Set.Icc 0 1) :
    ContinuousOn (primitive F Cα ell η S B base) (Set.Icc 0 1) := by
  have hi := integrand_intervalIntegrable hFm hF hint η S B
  have he : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := uIcc_of_le (by norm_num)
  have hc := intervalIntegral.continuousOn_primitive_interval' hi (he.symm ▸ hb)
  rw [he] at hc
  exact hc.const_mul (Cα * ell)

lemma primitive_derivative {F : ℝ → ℝ} (hFc : Continuous F)
    (hF : ∀ y, 0 ≤ y → 0 < F y)
    (hint : IntervalIntegrable (singularKernel F) volume 0 1)
    (Cα ell η S B : ℝ) {base a : ℝ} (hb : base ∈ Set.Icc 0 1) (ha : a ∈ Set.Ioc 0 1) :
    HasDerivAt (primitive F Cα ell η S B base)
      (Cα * ell * ((S - (1 + η) * B / a) / F (Real.log (1 / a)))) a := by
  have hi := integrand_intervalIntegrable hFc.measurable hF hint η S B
  have him : Measurable (fun s => (S - (1 + η) * B / s) / F (Real.log (1 / s))) := by
    fun_prop
  have hc : ContinuousAt (fun s => (S - (1 + η) * B / s) / F (Real.log (1 / s))) a := by
    apply ContinuousAt.div
    · fun_prop (disch := exact ha.1.ne')
    · exact hFc.continuousAt.comp (((continuousAt_const.div continuousAt_id ha.1.ne').log
        (div_ne_zero one_ne_zero ha.1.ne')))
    · exact (hF _ (log_inverse_nonneg ha)).ne'
  have hi' : IntervalIntegrable (fun s => (S - (1 + η) * B / s) / F (Real.log (1 / s))) volume base a :=
    hi.mono_set (by
      rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact uIcc_subset_Icc hb ⟨ha.1.le, ha.2⟩)
  exact (intervalIntegral.integral_hasDerivAt_right hi'
    him.stronglyMeasurable.stronglyMeasurableAtFilter hc).const_mul (Cα * ell)

lemma log_inverse_tendsto : Tendsto (fun s : ℝ => Real.log (1 / s)) (𝓝[>] 0) atTop := by
  simpa only [one_div, Real.log_inv, Function.comp_def] using
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero

lemma polynomial_log_decay (p : Polynomial ℝ) :
    Tendsto (fun s : ℝ => s * p.eval (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0) := by
  have ht := p.tendsto_div_exp_atTop.comp log_inverse_tendsto
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have he : Real.exp (Real.log (1 / s)) = 1 / s :=
    Real.exp_log (div_pos one_pos hs)
  dsimp only [Function.comp_def]
  rw [he]
  simp [div_eq_mul_inv, mul_comm]

lemma quadratic_lower_tendsto {F : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hF : ∀ y, 0 ≤ y → c * (1 + y)^2 ≤ F y) : Tendsto F atTop atTop := by
  have ht : Tendsto (fun y : ℝ => c * y) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  apply tendsto_atTop_mono' atTop _ ht
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  exact (show c * y ≤ c * (1 + y)^2 by nlinarith [sq_nonneg y]).trans (hF y hy)

lemma singular_tendsto {F : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hF : ∀ y, 0 ≤ y → c * (1 + y)^2 ≤ F y)
    (hdecay : Tendsto (fun s : ℝ => s * F (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (singularKernel F) (𝓝[>] 0) atTop := by
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, s * F (Real.log (1 / s)) ∈ Set.Ioi 0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with s hs hs1
    have hp : 0 < c * (1 + Real.log (1 / s))^2 := by
      have := log_inverse_nonneg ⟨hs, hs1⟩
      positivity
    exact mul_pos hs (hp.trans_le (hF _ (log_inverse_nonneg ⟨hs, hs1⟩)))
  have ht := tendsto_inv_nhdsGT_zero.comp
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hdecay hpos)
  change Tendsto (fun s => (1 / F (Real.log (1 / s))) / s) (𝓝[>] 0) atTop
  simpa only [Function.comp_def, one_div, div_eq_mul_inv, mul_inv_rev, one_mul] using ht

lemma integrand_tendsto_atBot {F : ℝ → ℝ} {c η S B : ℝ} (hc : 0 < c)
    (hF : ∀ y, 0 ≤ y → c * (1 + y)^2 ≤ F y)
    (hdecay : Tendsto (fun s : ℝ => s * F (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0))
    (hη : 0 ≤ η) (hB : 0 < B) :
    Tendsto (fun s => (S - (1 + η) * B / s) / F (Real.log (1 / s))) (𝓝[>] 0) atBot := by
  have hk : Tendsto (kernel F) (𝓝[>] 0) (𝓝 0) := by
    change Tendsto (fun s : ℝ => 1 / F (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0)
    exact
      (tendsto_const_nhds.div_atTop ((quadratic_lower_tendsto hc hF).comp log_inverse_tendsto) :
        Tendsto (fun s : ℝ => 1 / F (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0))
  have hs := (singular_tendsto hc hF hdecay).const_mul_atTop
    (show 0 < (1 + η) * B by positivity)
  have hn := tendsto_neg_atTop_atBot.comp hs
  have ht := (hk.const_mul S).add_atBot hn
  simp_rw [integrand_affine]
  exact ht

lemma primitive_inward_atBot {F : ℝ → ℝ} {c Cα ell η B base : ℝ}
    (hFc : Continuous F) (hc : 0 < c)
    (hF : ∀ y, 0 ≤ y → c * (1 + y)^2 ≤ F y)
    (hdecay : Tendsto (fun s : ℝ => s * F (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0))
    (hCα : 0 < Cα) (hell : 0 < ell) (hη : 0 ≤ η) (hB : 0 < B)
    (S : ℝ) (hb : base ∈ Set.Icc 0 1) :
    Tendsto (fun a => (primitive F Cα ell η S B base a -
      primitive F Cα ell η S B base 0) / a) (𝓝[>] 0) atBot := by
  have hp : ∀ y, 0 ≤ y → 0 < F y := fun y hy =>
    (show 0 < c * (1 + y)^2 by positivity).trans_le (hF y hy)
  have hi := singular_intervalIntegrable_of_quadratic hFc.measurable hc hF
  apply HasDerivAt.lhopital_zero_right_on_Ico (b := 1) (show (0 : ℝ) < 1 by norm_num)
    (f' := fun a => Cα * ell * ((S - (1 + η) * B / a) / F (Real.log (1 / a))))
    (g' := fun _ => 1)
  · intro a ha
    exact (primitive_derivative hFc hp hi Cα ell η S B hb ⟨ha.1, ha.2.le⟩).sub_const _
  · intro a _
    exact hasDerivAt_id a
  · exact ((primitive_continuousOn hFc.measurable hp hi Cα ell η S B hb).mono Ico_subset_Icc_self).sub continuousOn_const
  · exact continuous_id.continuousOn
  · intro _ _; exact one_ne_zero
  · simp
  · rfl
  · simpa only [div_one] using
      (integrand_tendsto_atBot hc hF hdecay hη hB).const_mul_atBot (mul_pos hCα hell)

lemma regular_quadratic_lower {h y : ℝ} (hh : 1 ≤ h) (hy : 0 ≤ y) :
    (1 / h) * (1 + y)^2 ≤ regularF h y := by
  dsimp [regularF]
  rw [one_div, mul_comm (h⁻¹), ← div_eq_mul_inv]
  apply div_le_div_of_nonneg_right _ (by linarith)
  nlinarith

lemma regular_decay (h : ℝ) :
    Tendsto (fun s : ℝ => s * regularF h (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0) := by
  have ht := polynomial_log_decay ((Polynomial.C h + Polynomial.X)^2 * Polynomial.C (1 / h))
  simpa [regularF, div_eq_mul_inv] using ht

lemma marked_decay (u H : ℝ) :
    Tendsto (fun s : ℝ => s * markedF u H (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0) := by
  have ht := polynomial_log_decay (Polynomial.C u + Polynomial.C H * Polynomial.X * (1 + Polynomial.X))
  simpa [markedF] using ht

lemma marked_lower_constant {u H : ℝ} (hu : 0 < u) (hH : 0 < H) :
    ∃ c, 0 < c ∧ ∀ y, 0 ≤ y → c * (1 + y)^2 ≤ markedF u H y := by
  refine ⟨min u (H / 2), lt_min hu (by positivity), ?_⟩
  intro y hy
  exact marked_quadratic_lower hy (lt_min hu (by positivity)) (min_le_left _ _)
    (by linarith [min_le_right u (H / 2)])

lemma regular_inward_atBot {h Cα ell η B base : ℝ}
    (hh : 1 ≤ h) (hCα : 0 < Cα) (hell : 0 < ell) (hη : 0 ≤ η) (hB : 0 < B)
    (S : ℝ) (hb : base ∈ Set.Icc 0 1) :
    Tendsto (fun a => (primitive (regularF h) Cα ell η S B base a -
      primitive (regularF h) Cα ell η S B base 0) / a) (𝓝[>] 0) atBot := by
  exact primitive_inward_atBot (by unfold regularF; fun_prop)
    (show 0 < 1 / h by positivity) (fun _ hy => regular_quadratic_lower hh hy)
    (regular_decay h) hCα hell hη hB S hb

lemma marked_singular_intervalIntegrable {u H : ℝ} (hu : 0 < u) (hH : 0 < H) :
    IntervalIntegrable (singularKernel (markedF u H)) volume 0 1 := by
  obtain ⟨c, hc, hF⟩ := marked_lower_constant hu hH
  exact singular_intervalIntegrable_of_quadratic (by unfold markedF; fun_prop) hc hF

lemma marked_inward_atBot {u H Cα ell η B base : ℝ}
    (hu : 0 < u) (hH : 0 < H) (hCα : 0 < Cα) (hell : 0 < ell) (hη : 0 ≤ η) (hB : 0 < B)
    (S : ℝ) (hb : base ∈ Set.Icc 0 1) :
    Tendsto (fun a => (primitive (markedF u H) Cα ell η S B base a -
      primitive (markedF u H) Cα ell η S B base 0) / a) (𝓝[>] 0) atBot := by
  obtain ⟨c, hc, hF⟩ := marked_lower_constant hu hH
  exact primitive_inward_atBot (by unfold markedF; fun_prop)
    hc hF (marked_decay u H) hCα hell hη hB S hb

/-- Elementary exponential estimate giving the marked contribution's side cancellation. -/
lemma exp_marked_bound {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-y) * y * (1 + y) ≤ 2 * (1 - Real.exp (-y)) := by
  have he := mul_le_mul_of_nonneg_left (Real.quadratic_le_exp_of_nonneg hy)
    (Real.exp_nonneg (-y))
  have hid : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  rw [hid] at he
  nlinarith [mul_nonneg (Real.exp_nonneg (-y)) hy]

lemma exp_square_bound {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-y) * y^2 ≤ 8 * Real.exp (-y / 2) := by
  have hp := Real.quadratic_le_exp_of_nonneg (show 0 ≤ y / 2 by positivity)
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_nonneg (-y))
  have he : Real.exp (-y) * Real.exp (y / 2) = Real.exp (-y / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he] at hm
  nlinarith [Real.exp_nonneg (-y), mul_nonneg (Real.exp_nonneg (-y)) hy]

lemma regular_exp_tail {h y : ℝ} (hh : 1 ≤ h) (hy : 4 * h < y) :
    Real.exp (-y) * regularF h y ≤ 32 * Real.exp (-h) := by
  have hh0 : 0 < h := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hp : regularF h y ≤ 4 * y^2 := by
    apply (div_le_iff₀ hh0).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg y)]
  calc
    _ ≤ Real.exp (-y) * (4 * y^2) := mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)
    _ = 4 * (Real.exp (-y) * y^2) := by ring
    _ ≤ 32 * Real.exp (-y / 2) := by nlinarith [exp_square_bound hy0]
    _ ≤ 32 * Real.exp (-h) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

lemma regular_coordinate_bound {h a : ℝ} (hh : 1 ≤ h) (ha : a ∈ Set.Icc 0 1) :
    a * regularF h (Real.log (1 / a)) ≤ 25 * a * h + 32 * Real.exp (-h) := by
  rcases eq_or_lt_of_le ha.1 with h0 | hp
  · subst a; simp only [zero_mul]; positivity
  have hlog := log_inverse_nonneg ⟨hp, ha.2⟩
  by_cases hc : Real.log (1 / a) ≤ 4 * h
  · have hreg : regularF h (Real.log (1 / a)) ≤ 25 * h := by
      apply (div_le_iff₀ (show 0 < h by linarith)).mpr
      nlinarith [sq_nonneg (4 * h - Real.log (1 / a))]
    have := mul_le_mul_of_nonneg_left hreg ha.1
    have := Real.exp_nonneg (-h)
    nlinarith
  · have he : Real.exp (-Real.log (1 / a)) = a := by
      rw [Real.exp_neg, Real.exp_log (div_pos one_pos hp)]
      simp
    have ht := regular_exp_tail hh (lt_of_not_ge hc)
    rw [he] at ht
    have : 0 ≤ 25 * a * h := by positivity
    linarith

lemma marked_coordinate_bound {u H a : ℝ} (hH : 0 ≤ H) (ha : a ∈ Set.Icc 0 1) :
    a * markedF u H (Real.log (1 / a)) ≤ a * u + 2 * H * (1 - a) := by
  rcases eq_or_lt_of_le ha.1 with h0 | hp
  · subst a; simp only [zero_mul, sub_zero, zero_add, mul_one]; positivity
  have he : Real.exp (-Real.log (1 / a)) = a := by
    rw [Real.exp_neg, Real.exp_log (div_pos one_pos hp)]
    simp
  have ht := exp_marked_bound (log_inverse_nonneg ⟨hp, ha.2⟩)
  rw [he] at ht
  have hm := mul_le_mul_of_nonneg_left ht hH
  dsimp [markedF]
  nlinarith

/-- Logarithmic comparison primitive on the upper half of the marked integral. -/
def affineLogTail (u H s : ℝ) : ℝ := -Real.log (u - H * Real.log s) / H

lemma affineLogTail_derivative {u H s : ℝ} (hu : 0 < u) (hH : 0 < H)
    (hs : s ∈ Set.Ioc 0 1) :
    HasDerivAt (affineLogTail u H) (1 / (s * (u - H * Real.log s))) s := by
  have hx : 0 < u - H * Real.log s := by
    have := mul_nonpos_of_nonneg_of_nonpos hH.le (Real.log_nonpos hs.1.le hs.2)
    linarith
  have hd := (((hasDerivAt_const s u).sub
    ((Real.hasDerivAt_log hs.1.ne').const_mul H)).log hx.ne').neg.div_const H
  convert hd using 1
  all_goals first | rfl | (dsimp; field_simp [hH.ne', hs.1.ne', hx.ne']; ring)

lemma marked_lower_half_bound {u H s : ℝ} (hu : 0 ≤ u) (hH : 0 < H)
    (hs : s ∈ Set.Icc 0 (Real.exp (-1))) :
    singularKernel (markedF u H) s ≤ (4 / H) * singularKernel (regularF 1) s := by
  rcases eq_or_lt_of_le hs.1 with hz | hp
  · subst s; simp [singularKernel]
  have hy : 1 ≤ Real.log (1 / s) := by
    have ht := Real.log_le_log hp hs.2
    rw [Real.log_exp] at ht
    rw [one_div, Real.log_inv]
    linarith
  have hden : (H / 4) * (1 + Real.log (1 / s))^2 ≤ markedF u H (Real.log (1 / s)) := by
    dsimp [markedF]
    have hq : (1 + Real.log (1 / s))^2 ≤ 4 * Real.log (1 / s) * (1 + Real.log (1 / s)) := by
      nlinarith
    have := mul_le_mul_of_nonneg_left hq hH.le
    nlinarith
  have hpos : 0 < (H / 4) * (1 + Real.log (1 / s))^2 := by positivity
  have hi := div_le_div_of_nonneg_right (one_div_le_one_div_of_le hpos hden) hp.le
  have he : (1 / ((H / 4) * (1 + Real.log (1 / s))^2)) / s =
      (4 / H) * singularKernel (regularF 1) s := by
    dsimp [singularKernel, kernel, regularF]
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  rw [he] at hi
  exact hi

lemma marked_singular_integral_bound {u H : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (hH : H = 1 + Real.log (1 / u)) :
    ∫ s in (0 : ℝ)..1, singularKernel (markedF u H) s ≤ 4 := by
  have hlogu : Real.log u ≤ 0 := Real.log_nonpos hu.le hu1
  have hHe : H = 1 - Real.log u := by rw [hH, one_div, Real.log_inv]; ring
  have hH1 : 1 ≤ H := by linarith
  have hHp : 0 < H := by linarith
  let b := Real.exp (-1)
  have hb0 : 0 < b := Real.exp_pos _
  have hb1 : b ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hbm : b ∈ Set.Icc (0 : ℝ) 1 := ⟨hb0.le, hb1⟩
  have hlogb : Real.log b = -1 := Real.log_exp _
  have hir := regular_singular_intervalIntegrable (by norm_num : (0 : ℝ) < 1)
  have him := marked_singular_intervalIntegrable hu hHp
  have hsub0 : Set.uIcc (0 : ℝ) b ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact uIcc_subset_Icc ⟨le_rfl, by norm_num⟩ hbm
  have hsub1 : Set.uIcc b 1 ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact uIcc_subset_Icc hbm ⟨by norm_num, le_rfl⟩
  have hregval : ∫ s in (0 : ℝ)..b, singularKernel (regularF 1) s = 1 / 2 := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb0.le
      ((regularTail_continuousOn (by norm_num : (0 : ℝ) < 1)).mono (Icc_subset_Icc le_rfl hb1))
      (fun s (hs : s ∈ Set.Ioo 0 b) => by
        rw [regular_singular_formula]
        exact regularTail_derivative (by norm_num) ⟨hs.1, hs.2.le.trans hb1⟩)
      (hir.mono_set hsub0)
    rw [regularTail_zero, regularTail_of_ne hb0.ne', hlogb] at he
    norm_num at he
    exact he
  have hlow : ∫ s in (0 : ℝ)..b, singularKernel (markedF u H) s ≤ 2 / H := by
    have he := intervalIntegral.integral_mono_on hb0.le (him.mono_set hsub0)
      ((hir.mono_set hsub0).const_mul (4 / H))
      (fun s hs => marked_lower_half_bound hu.le hHp hs)
    rw [intervalIntegral.integral_const_mul, hregval] at he
    convert he using 1
    ring
  have hafc : ContinuousOn (fun s => 1 / (s * (u - H * Real.log s))) (Set.Icc b 1) := by
    intro s hs
    have hs0 : 0 < s := hb0.trans_le hs.1
    have hden : u - H * Real.log s ≠ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos hHp.le (Real.log_nonpos hs0.le hs.2)
      linarith
    exact ((continuousAt_const.div
      (continuousAt_id.mul (continuousAt_const.sub
        ((Real.continuousAt_log hs0.ne').const_mul H))) (mul_ne_zero hs0.ne' hden))).continuousWithinAt
  have hafint : IntervalIntegrable
      (fun s => 1 / (s * (u - H * Real.log s))) volume b 1 :=
    hafc.intervalIntegrable_of_Icc hb1
  have hafval : ∫ s in b..1, 1 / (s * (u - H * Real.log s)) =
      (Real.log (u + H) - Real.log u) / H := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb1
      (fun s hs => (affineLogTail_derivative hu hHp ⟨hb0.trans_le hs.1, hs.2⟩).continuousAt.continuousWithinAt)
      (fun s hs => affineLogTail_derivative hu hHp ⟨hb0.trans hs.1, hs.2.le⟩) hafint
    dsimp [affineLogTail] at he
    rw [Real.log_one, hlogb] at he
    simp only [mul_zero, sub_zero, mul_neg_one, sub_neg_eq_add] at he
    rw [he]
    ring
  have hup : ∫ s in b..1, singularKernel (markedF u H) s ≤
      (Real.log (u + H) - Real.log u) / H := by
    rw [← hafval]
    apply intervalIntegral.integral_mono_on hb1 (him.mono_set hsub1) hafint
    intro s hs
    have hs0 : 0 < s := hb0.trans_le hs.1
    have hy := log_inverse_nonneg ⟨hs0, hs.2⟩
    have he : u - H * Real.log s = u + H * Real.log (1 / s) := by
      rw [one_div, Real.log_inv]; ring
    rw [he]
    have hp : 0 < u + H * Real.log (1 / s) := by positivity
    have hf : u + H * Real.log (1 / s) ≤ markedF u H (Real.log (1 / s)) := by
      dsimp [markedF]; nlinarith [mul_nonneg hHp.le (sq_nonneg (Real.log (1 / s)))]
    have hi := div_le_div_of_nonneg_right (one_div_le_one_div_of_le hp hf) hs0.le
    convert hi using 1
    all_goals first | rfl | simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
  have hlog : Real.log (u + H) ≤ H := by
    have h₁ := Real.log_le_log (show 0 < u + H by positivity) (show u + H ≤ 1 + H by linarith)
    have h₂ := Real.log_le_sub_one_of_pos (show 0 < 1 + H by positivity)
    linarith
  have hfup : (Real.log (u + H) - Real.log u) / H ≤ 2 := by
    apply (div_le_iff₀ hHp).mpr
    linarith
  have hflow : 2 / H ≤ 2 := by apply (div_le_iff₀ hHp).mpr; linarith
  have htotal := intervalIntegral.integral_add_adjacent_intervals (him.mono_set hsub0) (him.mono_set hsub1)
  linarith

open scoped BigOperators

lemma regular_denominator_sum {ι : Type*} [Fintype ι] {a h : ι → ℝ} {C : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : ∑ i, a i = 1) (hh : ∀ i, 1 ≤ h i)
    (hC : ∑ i, Real.exp (-h i) ≤ C) :
    ∑ i, a i * regularF (h i) (Real.log (1 / a i)) ≤
      (25 + 32 * C) * ∑ i, a i * h i := by
  have hmax : ∀ i, a i ≤ 1 := fun i => by
    simpa only [hasum] using Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
  have hT : 1 ≤ ∑ i, a i * h i := by
    rw [← hasum]
    exact Finset.sum_le_sum fun i _ => le_mul_of_one_le_right (ha i) (hh i)
  have hCn : 0 ≤ C := (Finset.sum_nonneg fun i _ => Real.exp_nonneg _).trans hC
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => regular_coordinate_bound (hh i) ⟨ha i, hmax i⟩
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc] at hs
  have he := mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 32)
  have hCT := mul_le_mul_of_nonneg_left hT (show 0 ≤ 32 * C by positivity)
  nlinarith

lemma marked_denominator_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a h : ι → ℝ} {u H c C : ℝ} (o : ι)
    (ha : ∀ i, 0 ≤ a i) (hasum : ∑ i, a i = 1)
    (hu : 0 ≤ u) (huH : u ≤ H) (hc : 0 < c) (hc1 : c ≤ 1)
    (hh : ∀ i ≠ o, 1 ≤ h i) (hside : ∀ i ≠ o, c * H ≤ h i)
    (hC0 : 0 ≤ C) (hC : ∑ i ∈ Finset.univ.erase o, Real.exp (-h i) ≤ C * u) :
    a o * markedF u H (Real.log (1 / a o)) +
      ∑ i ∈ Finset.univ.erase o, a i * regularF (h i) (Real.log (1 / a i)) ≤
    ((25 * c + 2 + 32 * C) / c) *
      (a o * u + ∑ i ∈ Finset.univ.erase o, a i * h i) := by
  let T := a o * u + ∑ i ∈ Finset.univ.erase o, a i * h i
  have hmax : ∀ i, a i ≤ 1 := fun i => by
    simpa only [hasum] using Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
  have hsum : (∑ i ∈ Finset.univ.erase o, a i) = 1 - a o := by
    have he := Finset.sum_erase_add Finset.univ a (Finset.mem_univ o)
    rw [hasum] at he
    linarith
  have hside0 : 0 ≤ ∑ i ∈ Finset.univ.erase o, a i * h i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (ha i) (le_trans (by norm_num) (hh i (Finset.mem_erase.mp hi).1))
  have hT0 : 0 ≤ T := add_nonneg (mul_nonneg (ha o) hu) hside0
  have hTs : c * H * (1 - a o) ≤ ∑ i ∈ Finset.univ.erase o, a i * h i := by
    rw [← hsum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    nlinarith [mul_le_mul_of_nonneg_left (hside i (Finset.mem_erase.mp hi).1) (ha i)]
  have hcuT : c * u ≤ T := by
    dsimp [T]
    have hcuH := mul_le_mul_of_nonneg_left huH hc.le
    have hm := mul_le_mul_of_nonneg_right hcuH (sub_nonneg.mpr (hmax o))
    have hca := mul_le_mul_of_nonneg_right hc1 (mul_nonneg (ha o) hu)
    nlinarith
  have hsm := marked_coordinate_bound (hu.trans huH) ⟨ha o, hmax o⟩ (u := u)
  have hsr := Finset.sum_le_sum fun i (hi : i ∈ Finset.univ.erase o) =>
    regular_coordinate_bound (hh i (Finset.mem_erase.mp hi).1) ⟨ha i, hmax i⟩
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc] at hsr
  have htail := mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 32)
  have hraw : a o * markedF u H (Real.log (1 / a o)) +
      ∑ i ∈ Finset.univ.erase o, a i * regularF (h i) (Real.log (1 / a i)) ≤
      25 * T + 2 * H * (1 - a o) + 32 * C * u := by
    dsimp [T]
    nlinarith [mul_nonneg (ha o) hu]
  have hHpay : c * (H * (1 - a o)) ≤ T := by
    dsimp [T]
    nlinarith [mul_nonneg (ha o) hu]
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    _ ≤ c * (25 * T + 2 * H * (1 - a o) + 32 * C * u) := mul_le_mul_of_nonneg_left hraw hc.le
    _ ≤ (25 * c + 2 + 32 * C) * T := by
      have ht := mul_le_mul_of_nonneg_left hcuT (show 0 ≤ 32 * C by positivity)
      nlinarith
    _ = c * (((25 * c + 2 + 32 * C) / c) * T) := by field_simp

end KServer.SimplexAnalytic

namespace KServer.SimplexAnalytic
open Set MeasureTheory
open scoped BigOperators

lemma log_inverse_nonneg_closed {s : ℝ} (hs : s ∈ Set.Icc 0 1) :
    0 ≤ Real.log (1 / s) := by
  rcases eq_or_lt_of_le hs.1 with hz | hp
  · subst s; simp
  · exact log_inverse_nonneg ⟨hp, hs.2⟩

lemma primitive_affine {F : ℝ → ℝ} (hFm : Measurable F)
    (hF : ∀ y, 0 ≤ y → 0 < F y)
    (hint : IntervalIntegrable (singularKernel F) volume 0 1)
    (Cα ell η S B : ℝ) {base a : ℝ} (hb : base ∈ Set.Icc 0 1) (ha : a ∈ Set.Icc 0 1) :
    primitive F Cα ell η S B base a = Cα * ell *
      (S * (∫ s in base..a, kernel F s) -
        (1 + η) * B * (∫ s in base..a, singularKernel F s)) := by
  have hsub : Set.uIcc base a ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact uIcc_subset_Icc hb ha
  unfold primitive
  simp_rw [integrand_affine]
  rw [intervalIntegral.integral_sub (((kernel_intervalIntegrable hFm hF hint).mono_set hsub).const_mul S)
    ((hint.mono_set hsub).const_mul ((1 + η) * B))]
  simp only [intervalIntegral.integral_const_mul]

lemma regularF_lower {h y : ℝ} (hh : 0 < h) (hy : 0 ≤ y) : h ≤ regularF h y := by
  unfold regularF
  apply (le_div_iff₀ hh).mpr
  nlinarith

lemma regular_kernel_bounds {h s : ℝ} (hh : 1 ≤ h) (hs : s ∈ Set.Icc 0 1) :
    0 ≤ kernel (regularF h) s ∧ kernel (regularF h) s ≤ 1 := by
  have hp : 0 < h := by linarith
  have hf := regularF_lower hp (log_inverse_nonneg_closed hs)
  constructor
  · exact div_nonneg (by norm_num) (hp.le.trans hf)
  · dsimp [kernel]
    exact (div_le_one (hp.trans_le hf)).mpr (hh.trans hf)

lemma regular_coefficients {h a : ℝ} (hh : 1 ≤ h) (ha : a ∈ Set.Icc 0 1) :
    (∫ s in (0 : ℝ)..a, kernel (regularF h) s) ∈ Set.Icc 0 a ∧
    (∫ s in (0 : ℝ)..a, singularKernel (regularF h) s) ∈ Set.Icc 0 1 := by
  have hp : 0 < h := by linarith
  have hF : ∀ y, 0 ≤ y → 0 < regularF h y := fun y hy => hp.trans_le (regularF_lower hp hy)
  have hi := regular_singular_intervalIntegrable hp
  have hki := kernel_intervalIntegrable (by unfold regularF; fun_prop) hF hi
  have hsub : Set.uIcc (0 : ℝ) a ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact uIcc_subset_Icc ⟨le_rfl, by norm_num⟩ ha
  have hn : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ singularKernel (regularF h) s := by
    intro s hs
    exact div_nonneg (regular_kernel_bounds hh hs).1 hs.1
  constructor
  · constructor
    · exact intervalIntegral.integral_nonneg ha.1 fun s hs => (regular_kernel_bounds hh ⟨hs.1, hs.2.trans ha.2⟩).1
    · have he := intervalIntegral.integral_mono_on ha.1 (hki.mono_set hsub)
        (intervalIntegrable_const (μ := volume)) (fun s hs => (regular_kernel_bounds hh ⟨hs.1, hs.2.trans ha.2⟩).2)
      simpa using he
  · constructor
    · exact intervalIntegral.integral_nonneg ha.1 fun s hs => hn s ⟨hs.1, hs.2.trans ha.2⟩
    · rw [← regular_singular_integral hp]
      apply intervalIntegral.integral_mono_interval le_rfl ha.1 ha.2 _ hi
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hn s ⟨hs.1.le, hs.2⟩

lemma regular_component_bound {h a Cα ell η S B : ℝ}
    (hh : 1 ≤ h) (ha : a ∈ Set.Icc 0 1) (hC : 0 ≤ Cα) (hl : 0 ≤ ell)
    (hη : 0 ≤ η) (hS : 0 ≤ S) (hB : 0 ≤ B) :
    |primitive (regularF h) Cα ell η S B 0 a| ≤
      Cα * ell * (S * a + (1 + η) * B) := by
  have hp : 0 < h := by linarith
  rw [primitive_affine (by unfold regularF; fun_prop)
    (fun y hy => hp.trans_le (regularF_lower hp hy))
    (regular_singular_intervalIntegrable hp) Cα ell η S B ⟨le_rfl, by norm_num⟩ ha]
  obtain ⟨hK, hJ⟩ := regular_coefficients hh ha
  rw [abs_mul, abs_of_nonneg (mul_nonneg hC hl)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hl)
  exact (abs_sub _ _).trans (by
    rw [abs_of_nonneg (mul_nonneg hS hK.1),
      abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith) hB) hJ.1)]
    nlinarith [mul_le_mul_of_nonneg_left hK.2 hS,
      mul_le_mul_of_nonneg_left hJ.2 (show 0 ≤ (1 + η) * B by positivity)])

lemma marked_positive {u H : ℝ} (hu : 0 < u) (hH : 0 ≤ H) :
    ∀ y, 0 ≤ y → 0 < markedF u H y := by
  intro y hy
  unfold markedF
  positivity

lemma marked_coefficients {u H a : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (hH : H = 1 + Real.log (1 / u)) (ha : a ∈ Set.Icc 0 1) :
    (∫ s in a..1, kernel (markedF u H) s) ∈ Set.Icc 0 4 ∧
    (∫ s in a..1, singularKernel (markedF u H) s) ∈ Set.Icc 0 4 := by
  have hH1 : 1 ≤ H := by rw [hH]; linarith [log_inverse_nonneg ⟨hu, hu1⟩]
  have hp : 0 < H := by linarith
  have hi := marked_singular_intervalIntegrable hu hp
  have hsub : Set.uIcc a 1 ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact uIcc_subset_Icc ha ⟨by norm_num, le_rfl⟩
  have hn : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ kernel (markedF u H) s := by
    intro s hs
    exact div_nonneg (by norm_num) (marked_positive hu hp.le _ (log_inverse_nonneg_closed hs)).le
  have hjn : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ singularKernel (markedF u H) s := by
    intro s hs
    exact div_nonneg (hn s hs) hs.1
  have hji : (∫ s in a..1, singularKernel (markedF u H) s) ∈ Set.Icc 0 4 := by
    constructor
    · exact intervalIntegral.integral_nonneg ha.2 fun s hs => hjn s ⟨ha.1.trans hs.1, hs.2⟩
    · apply le_trans _ (marked_singular_integral_bound hu hu1 hH)
      apply intervalIntegral.integral_mono_interval ha.1 ha.2 le_rfl _ hi
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hjn s ⟨hs.1.le, hs.2⟩
  refine ⟨⟨intervalIntegral.integral_nonneg ha.2 (fun s hs => hn s ⟨ha.1.trans hs.1, hs.2⟩), ?_⟩, hji⟩
  apply le_trans _ hji.2
  apply intervalIntegral.integral_mono_on_of_le_Ioo ha.2
    ((kernel_intervalIntegrable (by unfold markedF; fun_prop) (marked_positive hu hp.le) hi).mono_set hsub)
    (hi.mono_set hsub)
  intro s hs
  have hs0 : 0 < s := ha.1.trans_lt hs.1
  apply (le_div_iff₀ hs0).mpr
  exact mul_le_of_le_one_right (hn s ⟨hs0.le, hs.2.le⟩) hs.2.le

lemma marked_component_bound {u H a Cα ell η S B Bside : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hH : H = 1 + Real.log (1 / u))
    (ha : a ∈ Set.Icc 0 1) (hC : 0 ≤ Cα) (hl : 0 ≤ ell)
    (hη : 0 ≤ η) (hηu : η ≤ u) (hB : 0 ≤ B) (hside : 0 ≤ Bside)
    (hS : S = B + Bside) :
    |primitive (markedF u H) Cα ell η S B 1 a| ≤
      4 * Cα * ell * (S * (1 - a) + Bside + u * S) := by
  have hS0 : 0 ≤ S := by linarith
  have hH1 : 1 ≤ H := by rw [hH]; linarith [log_inverse_nonneg ⟨hu, hu1⟩]
  have hHp : 0 < H := by linarith
  let f := fun s => (S - (1 + η) * B / s) / markedF u H (Real.log (1 / s))
  let M := S * (1 - a) + Bside + u * S
  have hM : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg (add_nonneg (mul_nonneg hS0 (sub_nonneg.mpr ha.2)) hside) (mul_nonneg hu.le hS0)
  have hint := marked_singular_intervalIntegrable hu hHp
  have hsub : Set.uIcc a 1 ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact uIcc_subset_Icc ha ⟨by norm_num, le_rfl⟩
  have hfi : IntervalIntegrable f volume a 1 :=
    (integrand_intervalIntegrable (by unfold markedF; fun_prop)
      (marked_positive hu hHp.le) hint η S B).mono_set hsub
  have habs : IntervalIntegrable (fun s => |f s|) volume a 1 := by
    simpa only [Real.norm_eq_abs] using hfi.norm
  have hfbound : ∀ s ∈ Set.Ioo a 1, |f s| ≤ M * singularKernel (markedF u H) s := by
    intro s hs
    have hs0 : 0 < s := ha.1.trans_lt hs.1
    have hs1 : s ≤ 1 := hs.2.le
    have hj : 0 ≤ singularKernel (markedF u H) s :=
      div_nonneg (div_nonneg (by norm_num)
        (marked_positive hu hHp.le _ (log_inverse_nonneg ⟨hs0, hs1⟩)).le) hs0.le
    have he : f s = (S * (s - 1) + Bside - η * B) * singularKernel (markedF u H) s := by
      dsimp [f, singularKernel, kernel]
      rw [hS]
      field_simp
      ring
    rw [he, abs_mul, abs_of_nonneg hj]
    apply mul_le_mul_of_nonneg_right _ hj
    have hm := (abs_sub (S * (s - 1) + Bside) (η * B)).trans
      (add_le_add (abs_add_le (S * (s - 1)) Bside) le_rfl)
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hS0 (by linarith)),
      abs_of_nonneg hside, abs_of_nonneg (mul_nonneg hη hB)] at hm
    dsimp [M]
    have hsa := mul_le_mul_of_nonneg_left hs.1.le hS0
    have hηS := mul_le_mul_of_nonneg_left (show B ≤ S by linarith) hη
    have huS := mul_le_mul_of_nonneg_right hηu hS0
    linarith
  have hi : |∫ s in a..1, f s| ≤ 4 * M := by
    calc
      _ ≤ ∫ s in a..1, |f s| := intervalIntegral.abs_integral_le_integral_abs ha.2
      _ ≤ ∫ s in a..1, M * singularKernel (markedF u H) s :=
        intervalIntegral.integral_mono_on_of_le_Ioo ha.2 habs ((hint.mono_set hsub).const_mul M) hfbound
      _ = M * ∫ s in a..1, singularKernel (markedF u H) s := intervalIntegral.integral_const_mul _ _
      _ ≤ 4 * M := by
        have hj := (marked_coefficients hu hu1 hH ha).2.2
        nlinarith
  unfold primitive
  rw [intervalIntegral.integral_symm, abs_mul, abs_neg,
    abs_of_nonneg (mul_nonneg hC hl)]
  have hm := mul_le_mul_of_nonneg_left hi (mul_nonneg hC hl)
  change Cα * ell * |∫ s in a..1, f s| ≤ _
  convert hm using 1
  all_goals first | rfl | (dsimp [M]; ring)

/-- Dimension-free input bound for an affine sum of the exact primitives.
The scalar assumptions are the integral coefficient bounds established above. -/
lemma affine_sum_input_bound {ι : Type*} [Fintype ι]
    {K J η B B' : ι → ℝ} {L ηmax CK CJ : ℝ}
    (hL : 0 ≤ L) (hη : ∀ i, 0 ≤ η i) (hηmax : ∀ i, η i ≤ ηmax)
    (hK : ∑ i, |K i| ≤ CK) (hJ : ∀ i, |J i| ≤ CJ) :
    |(∑ i, L * ((∑ j, B j) * K i - (1 + η i) * B i * J i)) -
      (∑ i, L * ((∑ j, B' j) * K i - (1 + η i) * B' i * J i))| ≤
      L * (CK + (1 + ηmax) * CJ) * ∑ i, |B i - B' i| := by
  let T := ∑ i, |B i - B' i|
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hS : |(∑ j, B j) - ∑ j, B' j| ≤ T := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hCK : 0 ≤ CK := (Finset.sum_nonneg fun i _ => abs_nonneg _).trans hK
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |L * ((∑ j, B j) * K i - (1 + η i) * B i * J i) -
      L * ((∑ j, B' j) * K i - (1 + η i) * B' i * J i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, L * (T * |K i| + (1 + ηmax) * |B i - B' i| * CJ) := by
      apply Finset.sum_le_sum
      intro i _
      have he : L * ((∑ j, B j) * K i - (1 + η i) * B i * J i) -
          L * ((∑ j, B' j) * K i - (1 + η i) * B' i * J i) =
          L * (((∑ j, B j) - ∑ j, B' j) * K i - (1 + η i) * (B i - B' i) * J i) := by ring
      rw [he, abs_mul, abs_of_nonneg hL]
      apply mul_le_mul_of_nonneg_left _ hL
      apply (abs_sub _ _).trans
      simp only [abs_mul, abs_of_nonneg (show 0 ≤ 1 + η i by linarith [hη i])]
      apply add_le_add (mul_le_mul_of_nonneg_right hS (abs_nonneg _))
      have he := mul_le_mul_of_nonneg_right (show 1 + η i ≤ 1 + ηmax by linarith [hηmax i]) (abs_nonneg (B i - B' i))
      exact mul_le_mul he (hJ i) (abs_nonneg _)
        (mul_nonneg (by linarith [hη i, hηmax i]) (abs_nonneg _))
    _ ≤ L * (CK + (1 + ηmax) * CJ) * T := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      have hm := mul_le_mul_of_nonneg_left hK (mul_nonneg hL hT)
      dsimp [T] at *
      calc
        _ = (L * ∑ i, |B i - B' i|) * (∑ i, |K i|) + L * ((1 + ηmax) * (∑ i, |B i - B' i|) * CJ) := by ring
        _ ≤ (L * ∑ i, |B i - B' i|) * CK + L * ((1 + ηmax) * (∑ i, |B i - B' i|) * CJ) := add_le_add hm le_rfl
        _ = _ := by ring


/-- The exact regular-domain version of (alpha-input-slopes), with constant 3. -/
lemma regular_input_slopes {ι : Type*} [Fintype ι]
    {h η B B' a : ι → ℝ} {Cα ell : ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    (hh : ∀ i, 1 ≤ h i) (hη0 : ∀ i, 0 ≤ η i) (hη1 : ∀ i, η i ≤ 1)
    (hC : 0 ≤ Cα) (hl : 0 ≤ ell) :
    |(∑ i, primitive (regularF (h i)) Cα ell (η i) (∑ j, B j) (B i) 0 (a i)) -
      (∑ i, primitive (regularF (h i)) Cα ell (η i) (∑ j, B' j) (B' i) 0 (a i))| ≤
      3 * Cα * ell * ∑ i, |B i - B' i| := by
  have ha : ∀ i, a i ∈ Set.Icc 0 1 := by
    intro i
    refine ⟨ha0 i, ?_⟩
    rw [← ha1]
    exact Finset.single_le_sum (fun j _ => ha0 j) (Finset.mem_univ _)
  let K := fun i => ∫ s in (0 : ℝ)..a i, kernel (regularF (h i)) s
  let J := fun i => ∫ s in (0 : ℝ)..a i, singularKernel (regularF (h i)) s
  have hb := fun i => regular_coefficients (hh i) (ha i)
  have hK : ∑ i, |K i| ≤ 1 := by
    rw [← ha1]
    apply Finset.sum_le_sum
    intro i _
    rw [abs_of_nonneg (hb i).1.1]
    exact (hb i).1.2
  have hJ : ∀ i, |J i| ≤ 1 := by
    intro i
    rw [abs_of_nonneg (hb i).2.1]
    exact (hb i).2.2
  have he (V : ι → ℝ) :
      (∑ i, primitive (regularF (h i)) Cα ell (η i) (∑ j, V j) (V i) 0 (a i)) =
      ∑ i, (Cα * ell) * ((∑ j, V j) * K i - (1 + η i) * V i * J i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact primitive_affine (by unfold regularF; fun_prop)
      (fun y hy => (show 0 < h i by linarith [hh i]).trans_le
        (regularF_lower (by linarith [hh i]) hy))
      (regular_singular_intervalIntegrable (by linarith [hh i]))
      Cα ell (η i) (∑ j, V j) (V i) ⟨le_rfl, by norm_num⟩ (ha i)
  rw [he B, he B']
  have ht := affine_sum_input_bound (B := B) (B' := B') (mul_nonneg hC hl)
    hη0 hη1 hK hJ
  convert ht using 1
  ring

/-- The source marked-domain affine input bound, also uniform as u tends to 0. -/
lemma marked_input_slopes {ι : Type*} [Fintype ι] [DecidableEq ι] (o : ι)
    {h η B B' a : ι → ℝ} {Cα ell u H : ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    (hh : ∀ i, i ≠ o → 1 ≤ h i) (hu : 0 < u) (hu1 : u ≤ 1)
    (hH : H = 1 + Real.log (1 / u))
    (hη0 : ∀ i, 0 ≤ η i) (hη1 : ∀ i, η i ≤ 1)
    (hC : 0 ≤ Cα) (hl : 0 ≤ ell) :
    let F := fun i => if i = o then markedF u H else regularF (h i)
    let base := fun i => if i = o then (1 : ℝ) else 0
    |(∑ i, primitive (F i) Cα ell (η i) (∑ j, B j) (B i) (base i) (a i)) -
      (∑ i, primitive (F i) Cα ell (η i) (∑ j, B' j) (B' i) (base i) (a i))| ≤
      13 * Cα * ell * ∑ i, |B i - B' i| := by
  intro F base
  have ha : ∀ i, a i ∈ Set.Icc 0 1 := by
    intro i
    refine ⟨ha0 i, ?_⟩
    rw [← ha1]
    exact Finset.single_le_sum (fun j _ => ha0 j) (Finset.mem_univ _)
  have hH0 : 0 < H := by rw [hH]; linarith [log_inverse_nonneg ⟨hu, hu1⟩]
  let K := fun i => ∫ s in base i..a i, kernel (F i) s
  let J := fun i => ∫ s in base i..a i, singularKernel (F i) s
  have hKa : ∀ i, |K i| ≤ a i + if i = o then 4 else 0 := by
    intro i
    by_cases hi : i = o
    · subst i
      simp only [K, base, F, ite_true]
      rw [intervalIntegral.integral_symm, abs_neg,
        abs_of_nonneg (marked_coefficients hu hu1 hH (ha o)).1.1]
      linarith [(marked_coefficients hu hu1 hH (ha o)).1.2, ha0 o]
    · simp only [K, base, F, ite_eq_right hi, add_zero]
      rw [abs_of_nonneg (regular_coefficients (hh i hi) (ha i)).1.1]
      exact (regular_coefficients (hh i hi) (ha i)).1.2
  have hK : ∑ i, |K i| ≤ 5 := by
    have ht := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hKa i)
    norm_num [Finset.sum_add_distrib, ha1] at ht ⊢
    exact ht
  have hJ : ∀ i, |J i| ≤ 4 := by
    intro i
    by_cases hi : i = o
    · subst i
      simp only [J, base, F, ite_true]
      rw [intervalIntegral.integral_symm, abs_neg,
        abs_of_nonneg (marked_coefficients hu hu1 hH (ha o)).2.1]
      exact (marked_coefficients hu hu1 hH (ha o)).2.2
    · simp only [J, base, F, ite_eq_right hi]
      rw [abs_of_nonneg (regular_coefficients (hh i hi) (ha i)).2.1]
      linarith [(regular_coefficients (hh i hi) (ha i)).2.2]
  have he (V : ι → ℝ) :
      (∑ i, primitive (F i) Cα ell (η i) (∑ j, V j) (V i) (base i) (a i)) =
      ∑ i, (Cα * ell) * ((∑ j, V j) * K i - (1 + η i) * V i * J i) := by
    apply Finset.sum_congr rfl
    intro i _
    have hp : ∀ y, 0 ≤ y → 0 < F i y := by
      intro y hy
      dsimp [F]
      split_ifs with hi
      · exact marked_positive hu hH0.le y hy
      · exact (show 0 < h i by linarith [hh i hi]).trans_le
          (regularF_lower (by linarith [hh i hi]) hy)
    apply primitive_affine _ hp _ Cα ell (η i) (∑ j, V j) (V i) _ (ha i)
    · dsimp [F]; split_ifs
      · unfold markedF; fun_prop
      · unfold regularF; fun_prop
    · dsimp [F]; split_ifs with hi
      · exact marked_singular_intervalIntegrable hu hH0
      · exact regular_singular_intervalIntegrable (by linarith [hh i hi])
    · dsimp [base]; split_ifs <;> constructor <;> norm_num
  rw [he B, he B']
  have ht := affine_sum_input_bound (B := B) (B' := B') (mul_nonneg hC hl)
    hη0 hη1 hK hJ
  convert ht using 1
  ring

end KServer.SimplexAnalytic

end

end OAI
