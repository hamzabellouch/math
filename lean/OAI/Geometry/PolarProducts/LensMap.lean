import OAI.Geometry.PolarProducts.LogProfile

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology

open Set Filter Complex
open scoped Topology ContDiff

namespace PlanarLens
noncomputable section

def term (n : ℕ) (w : ℂ) : ℂ := (-1)^n * w^(2*n+1) / (2*n+1)^2

def termDeriv (n : ℕ) (w : ℂ) : ℂ := (-1)^n * w^(2*n) / (2*n+1)

def F (w : ℂ) : ℂ := (8 / (Real.pi^2) : ℝ) * ∑' n : ℕ, term n w

theorem hasDerivAt_term (n : ℕ) (w : ℂ) : HasDerivAt (term n) (termDeriv n w) w := by
  have hn : (2 * (n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)
  convert (((hasDerivAt_id w).pow (2*n+1)).const_mul ((-1 : ℂ)^n)).div_const
    ((2*(n : ℂ)+1)^2) using 1 <;> try rfl
  simp only [termDeriv, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.add_sub_cancel]
  field_simp [hn]
  rfl

@[simp] theorem term_zero (n : ℕ) : term n 0 = 0 := by simp [term]

@[simp] theorem F_zero : F 0 = 0 := by simp [F]

theorem norm_termDeriv_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {w : ℂ} (hw : ‖w‖ ≤ r) (n : ℕ) : ‖termDeriv n w‖ ≤ r^n := by
  have hn : (1 : ℝ) ≤ 2 * n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  calc
    ‖termDeriv n w‖ = ‖w‖^(2*n) / (2*n+1) := by
      simp only [termDeriv, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      congr 1
      norm_cast
    _ ≤ r^(2*n) := (div_le_self (pow_nonneg (norm_nonneg _) _) hn).trans
      (pow_le_pow_left₀ (norm_nonneg _) hw _)
    _ ≤ r^n := pow_le_pow_of_le_one hr hr1 (by omega)

theorem summable_termDeriv {w : ℂ} (hw : ‖w‖ < 1) : Summable (fun n => termDeriv n w) := by
  exact Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg w) hw)
    (norm_termDeriv_le (norm_nonneg w) hw.le le_rfl)

theorem hasDerivAt_F {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt F ((8 / (Real.pi^2) : ℝ) * ∑' n : ℕ, termDeriv n w) w := by
  obtain ⟨r, hwr, hr1⟩ := exists_between hw
  have hr : 0 < r := (norm_nonneg w).trans_lt hwr
  have hh := hasDerivAt_tsum_of_isPreconnected
    (summable_geometric_of_lt_one hr.le hr1) Metric.isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected
    (fun n z _ => hasDerivAt_term n z)
    (fun n z hz => norm_termDeriv_le hr.le hr1.le ((by simpa [Metric.mem_ball] using hz : ‖z‖ < r).le) n)
    (show (0 : ℂ) ∈ Metric.ball 0 r by simpa using hr)
    (show Summable (fun n => term n (0 : ℂ)) by simp)
    (show w ∈ Metric.ball 0 r by simpa using hwr)
  exact hh.const_mul _

theorem analyticOnNhd_F : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) 1) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro w hw
  exact (hasDerivAt_F (by simpa using hw)).differentiableAt.differentiableWithinAt

theorem mul_deriv_F {w : ℂ} (hw : ‖w‖ < 1) :
    w * deriv F w = (8 / (Real.pi^2) : ℝ) * Complex.arctan w := by
  rw [(hasDerivAt_F hw).deriv, mul_left_comm, ← tsum_mul_left]
  congr 1
  have he : (fun n : ℕ => w * termDeriv n w) =
      (fun n : ℕ => (-1)^n * w^(2*n+1) / (2*n+1)) := by
    funext n
    dsimp [termDeriv]
    rw [pow_succ]
    ring
  rw [he]
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using (Complex.hasSum_arctan hw).tsum_eq

theorem norm_term_le {w : ℂ} (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖term n w‖ ≤ 1 / ((n : ℝ)+1)^2 := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  calc
    ‖term n w‖ = ‖w‖^(2*n+1) / (2*(n : ℝ)+1)^2 := by
      simp only [term, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      congr 2
      norm_cast
    _ ≤ 1 / (2*(n : ℝ)+1)^2 := div_le_div_of_nonneg_right
      (pow_le_one₀ (norm_nonneg _) hw) (sq_nonneg _)
    _ ≤ 1 / ((n : ℝ)+1)^2 := one_div_le_one_div_of_le (sq_pos_of_pos hn)
      (pow_le_pow_left₀ hn.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith) 2)

theorem summable_bound : Summable (fun n : ℕ => 1 / ((n : ℝ)+1)^2) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))

theorem summable_term {w : ℂ} (hw : ‖w‖ ≤ 1) : Summable (fun n => term n w) :=
  Summable.of_norm_bounded summable_bound (norm_term_le hw)

theorem continuousOn_F_closedBall : ContinuousOn F (Metric.closedBall 0 1) := by
  apply ContinuousOn.const_mul _ _
  apply continuousOn_tsum (fun n => (by unfold term; fun_prop : Continuous (term n)).continuousOn)
    summable_bound
  intro n w hw
  exact norm_term_le (by simpa using hw) n

theorem F_norm_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖F w‖ ≤ (8 / Real.pi^2) * ∑' n : ℕ, 1 / ((n : ℝ)+1)^2 := by
  have hc : 0 ≤ 8 / Real.pi^2 := by positivity
  rw [F, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  exact (norm_tsum_le_tsum_norm (summable_term hw).norm).trans
    (Summable.tsum_le_tsum (norm_term_le hw) (summable_term hw).norm summable_bound)

@[simp] theorem F_neg (w : ℂ) : F (-w) = -F w := by
  have he : (fun n : ℕ => term n (-w)) = fun n : ℕ => -term n w := by
    funext n
    simp only [term]
    rw [(show Odd (2*n+1) by exact ⟨n, by omega⟩).neg_pow]
    ring
  simp only [F, he, tsum_neg, mul_neg]

@[simp] theorem F_conj (w : ℂ) : F ((starRingEnd ℂ) w) = (starRingEnd ℂ) (F w) := by
  have he : (fun n : ℕ => term n ((starRingEnd ℂ) w)) = fun n : ℕ => conjCLE (term n w) := by
    funext n
    simp [term, map_ofNat]
  simp only [F, he, ← conjCLE.map_tsum]
  simp [map_ofNat]

def cayley (w : ℂ) : ℂ := (1 + w*I)/(1-w*I)

theorem cayley_re (w : ℂ) : (cayley w).re = (1 - ‖w‖^2) / normSq (1-w*I) := by
  rw [cayley, div_re, Complex.sq_norm]
  simp only [add_re, one_re, mul_re, I_re, mul_zero, mul_im, I_im, mul_one,
    zero_sub, sub_re, add_im, one_im, sub_im, add_zero, zero_add, normSq_apply]
  ring

theorem cayley_im (w : ℂ) : (cayley w).im = 2*w.re / normSq (1-w*I) := by
  rw [cayley, div_im]
  simp only [add_re, one_re, mul_re, I_re, mul_zero, mul_im, I_im, mul_one,
    zero_sub, sub_re, add_im, one_im, sub_im, add_zero, zero_add]
  ring

theorem cayley_re_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayley w).re := by
  have hn : 1-w*I ≠ 0 := by
    intro h
    have he := congr_arg norm (sub_eq_zero.mp h)
    simp only [norm_one, norm_mul, norm_I, mul_one] at he
    linarith
  rw [cayley_re]
  exact div_pos (by nlinarith [norm_nonneg w]) (normSq_pos.mpr hn)

theorem arctan_re_eq {w : ℂ} (hw : ‖w‖ < 1) :
    (Complex.arctan w).re = (1/2 : ℝ) * Real.arctan (2*w.re/(1-‖w‖^2)) := by
  have harg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (cayley_re_pos hw)))
  have ht := Real.arctan_tan harg.1 harg.2
  rw [Complex.tan_arg, cayley_re, cayley_im] at ht
  have hn : normSq (1-w*I) ≠ 0 := by
    apply ne_of_gt
    have h := cayley_re_pos hw
    rw [cayley_re] at h
    exact (div_pos_iff.mp h).resolve_right (by rintro ⟨_, hneg⟩; exact (normSq_nonneg _).not_gt hneg) |>.2
  have he : (2*w.re/normSq (1-w*I)) / ((1-‖w‖^2)/normSq (1-w*I)) =
      2*w.re/(1-‖w‖^2) := by field_simp
  rw [he] at ht
  rw [Complex.arctan, mul_re]
  have hre : (-I / 2 : ℂ).re = 0 := by norm_num [div_re]
  have him : (-I / 2 : ℂ).im = -1/2 := by norm_num [div_im]
  rw [hre, him, zero_mul, log_im]
  change 0 - (-1/2) * (cayley w).arg = _
  rw [← ht]
  ring

theorem re_mul_deriv_F {w : ℂ} (hw : ‖w‖ < 1) :
    (w * deriv F w).re = (4 / Real.pi^2) * Real.arctan (2*w.re/(1-‖w‖^2)) := by
  rw [mul_deriv_F hw, re_ofReal_mul, arctan_re_eq hw]
  ring

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

theorem norm_one_add_mul_I_sq (w : ℂ) : ‖1+w*I‖^2 = 1-2*w.im+‖w‖^2 := by
  simp only [Complex.sq_norm, normSq_apply, add_re, one_re, mul_re, I_re, I_im,
    mul_zero, mul_one, zero_sub, add_im, one_im, mul_im, zero_add, add_zero]
  ring

theorem norm_one_sub_mul_I_sq (w : ℂ) : ‖1-w*I‖^2 = 1+2*w.im+‖w‖^2 := by
  simp only [Complex.sq_norm, normSq_apply, sub_re, one_re, mul_re, I_re, I_im,
    mul_zero, mul_one, zero_sub, sub_im, one_im, mul_im, add_zero]
  ring

theorem one_add_mul_I_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1+w*I ≠ 0 := by
  intro h
  have he : w*I = -1 := eq_neg_of_add_eq_zero_right h
  have hh := congr_arg norm he
  simp only [norm_mul, norm_I, mul_one, norm_neg, norm_one] at hh
  linarith

theorem one_sub_mul_I_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1-w*I ≠ 0 := by
  have h := one_add_mul_I_ne_zero (w := -w) (by simpa using hw)
  simpa only [neg_mul, sub_eq_add_neg] using h

theorem arctan_im_eq (w : ℂ) :
    (Complex.arctan w).im = -(1/2 : ℝ) * Real.log (‖1+w*I‖/‖1-w*I‖) := by
  rw [Complex.arctan, mul_im]
  have hre : (-I / 2 : ℂ).re = 0 := by norm_num [div_re]
  have him : (-I / 2 : ℂ).im = -1/2 := by norm_num [div_im]
  rw [hre, him, zero_mul, zero_add, log_re, norm_div]
  ring

theorem arctan_im_pos {w : ℂ} (hw : ‖w‖ < 1) (hi : 0 < w.im) :
    0 < (Complex.arctan w).im := by
  have ha : 0 < ‖1+w*I‖ := norm_pos_iff.mpr (one_add_mul_I_ne_zero hw)
  have hb : 0 < ‖1-w*I‖ := norm_pos_iff.mpr (one_sub_mul_I_ne_zero hw)
  have hab : ‖1+w*I‖ < ‖1-w*I‖ := by
    have h1 := norm_one_add_mul_I_sq w
    have h2 := norm_one_sub_mul_I_sq w
    nlinarith [norm_nonneg (1+w*I), norm_nonneg (1-w*I)]
  rw [arctan_im_eq]
  have := Real.log_neg (div_pos ha hb) ((div_lt_one hb).mpr hab)
  linarith

theorem arctan_im_neg {w : ℂ} (hw : ‖w‖ < 1) (hi : w.im < 0) :
    (Complex.arctan w).im < 0 := by
  have hb : 0 < ‖1-w*I‖ := norm_pos_iff.mpr (one_sub_mul_I_ne_zero hw)
  have hab : ‖1-w*I‖ < ‖1+w*I‖ := by
    have h1 := norm_one_add_mul_I_sq w
    have h2 := norm_one_sub_mul_I_sq w
    nlinarith [norm_nonneg (1+w*I), norm_nonneg (1-w*I)]
  rw [arctan_im_eq]
  have := Real.log_pos ((one_lt_div hb).mpr hab)
  linarith

theorem arctan_im_mul_nonneg {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ (Complex.arctan w).im * w.im := by
  rcases lt_trichotomy w.im 0 with hi | hi | hi
  · exact mul_nonneg_of_nonpos_of_nonpos (arctan_im_neg hw hi).le hi.le
  · simp [hi]
  · exact (mul_pos (arctan_im_pos hw hi) hi).le

theorem arctan_re_mul_nonneg {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ (Complex.arctan w).re * w.re := by
  rw [arctan_re_eq hw]
  have hn : 0 < 1-‖w‖^2 := by nlinarith [norm_nonneg w]
  rcases lt_trichotomy w.re 0 with hi | hi | hi
  · have hr : Real.arctan (2*w.re/(1-‖w‖^2)) < 0 :=
      Real.arctan_lt_zero.mpr (div_neg_of_neg_of_pos (by linarith) hn)
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hi.le
  · simp [hi]
  · have hr : 0 < Real.arctan (2*w.re/(1-‖w‖^2)) :=
      Real.arctan_pos.mpr (div_pos (by linarith) hn)
    positivity

theorem arctan_div_re_pos {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    0 < (Complex.arctan w / w).re := by
  rw [div_re, ← add_div]
  apply div_pos _ (Complex.normSq_pos.mpr hw0)
  have hr := arctan_re_mul_nonneg hw
  have hi := arctan_im_mul_nonneg hw
  by_cases hre : w.re = 0
  · have him : w.im ≠ 0 := by
      intro h; apply hw0; exact Complex.ext (by simpa using hre) (by simpa using h)
    rcases lt_or_gt_of_ne him with him | him
    · have := mul_pos_of_neg_of_neg (arctan_im_neg hw him) him
      linarith
    · have := mul_pos (arctan_im_pos hw him) him
      linarith
  · have hn : 0 < 1-‖w‖^2 := by nlinarith [norm_nonneg w]
    have hp : 0 < (Complex.arctan w).re * w.re := by
      rw [arctan_re_eq hw]
      rcases lt_or_gt_of_ne hre with hre | hre
      · have h := Real.arctan_lt_zero.mpr (div_neg_of_neg_of_pos
          (by linarith : 2*w.re < 0) hn)
        exact mul_pos_of_neg_of_neg (by linarith) hre
      · have h := Real.arctan_pos.mpr (div_pos (by linarith : 0 < 2*w.re) hn)
        positivity
    linarith

@[simp] theorem deriv_F_zero : deriv F 0 = (8 / Real.pi^2 : ℝ) := by
  rw [(hasDerivAt_F (by simp : ‖(0 : ℂ)‖ < 1)).deriv]
  have he : (∑' n : ℕ, termDeriv n 0) = 1 := by
    rw [tsum_eq_single 0]
    · simp [termDeriv]
    · intro n hn
      have h : 2*n ≠ 0 := by omega
      simp [termDeriv, h]
  rw [he, mul_one]

theorem deriv_F_re_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (deriv F w).re := by
  by_cases hw0 : w = 0
  · rw [hw0, deriv_F_zero, ofReal_re]
    positivity
  · have he : deriv F w = (8 / Real.pi^2 : ℝ) * (Complex.arctan w / w) := by
      apply (mul_left_cancel₀ hw0)
      rw [mul_deriv_F hw]
      field_simp
    rw [he, re_ofReal_mul]
    exact mul_pos (by positivity) (arctan_div_re_pos hw hw0)

theorem F_injOn : InjOn F (Metric.ball 0 1) := by
  intro x hx y hy hxy
  by_contra hn
  have hd : y-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, ‖x+(t : ℂ)*(y-x)‖ < 1 := by
    intro t ht
    have hh := (convex_ball (0 : ℂ) 1).add_smul_sub_mem hx hy ht
    simpa only [Metric.mem_ball, dist_zero_right, Complex.real_smul] using hh
  let H : ℝ → ℝ := fun t => (F (x+(t : ℂ)*(y-x))/(y-x)).re
  have hh : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt H (deriv F (x+(t : ℂ)*(y-x))).re t := by
    intro t ht
    have hf := (hasDerivAt_F (hseg t ht)).differentiableAt.hasDerivAt
    have hc := ((hasDerivAt_id (t : ℂ)).mul_const (y-x)).const_add x
    have hm := (hf.comp (t : ℂ) hc).div_const (y-x)
    have he : deriv F (x+(t : ℂ)*(y-x)) * (1*(y-x)) / (y-x) =
        deriv F (x+(t : ℂ)*(y-x)) := by field_simp
    rw [he] at hm
    exact hm.real_of_complex
  have hmono : StrictMonoOn H (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 1)
      (fun t ht => (hh t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hh t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    exact deriv_F_re_pos (hseg t (interior_subset ht))
  have hlt := hmono (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) < 1)
  simp only [H, ofReal_zero, zero_mul, add_zero, ofReal_one, one_mul, add_sub_cancel] at hlt
  rw [hxy] at hlt
  exact lt_irrefl _ hlt

theorem re_F_imaginary (t : ℝ) : (F ((t : ℂ)*I)).re = 0 := by
  have h : (starRingEnd ℂ) ((t : ℂ)*I) = -((t : ℂ)*I) := by simp
  have he := F_conj ((t : ℂ)*I)
  rw [h, F_neg] at he
  have hre := congr_arg Complex.re he
  simp only [neg_re, conj_re] at hre
  linarith

theorem re_F_pos {w : ℂ} (hw : ‖w‖ < 1) (hr : 0 < w.re) : 0 < (F w).re := by
  let H : ℝ → ℝ := fun t => (F ((t : ℂ)+(w.im : ℂ)*I)).re
  have hseg : ∀ t ∈ Icc 0 w.re, ‖(t : ℂ)+(w.im : ℂ)*I‖ < 1 := by
    intro t ht
    have he : ‖(t : ℂ)+(w.im : ℂ)*I‖^2 = t^2+w.im^2 := by
      rw [Complex.sq_norm]
      simp [normSq_apply, pow_two]
    have hh : ‖w‖^2 = w.re^2+w.im^2 := by
      rw [Complex.sq_norm]
      simp [normSq_apply, pow_two]
    have hn : ‖w‖^2 < 1 := by nlinarith [norm_nonneg w]
    nlinarith [norm_nonneg ((t : ℂ)+(w.im : ℂ)*I), ht.1, ht.2]
  have hh : ∀ t ∈ Icc 0 w.re, HasDerivAt H (deriv F ((t : ℂ)+(w.im : ℂ)*I)).re t := by
    intro t ht
    have hf := (hasDerivAt_F (hseg t ht)).differentiableAt.hasDerivAt
    have hm := hf.comp (t : ℂ) ((hasDerivAt_id _).add_const ((w.im : ℂ)*I))
    convert hm.real_of_complex using 1 <;> first | rfl | simp
  have hmono : StrictMonoOn H (Icc 0 w.re) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 w.re)
      (fun t ht => (hh t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hh t (interior_subset ht)).hasDerivWithinAt)
    exact fun t ht => deriv_F_re_pos (hseg t (interior_subset ht))
  have hlt := hmono ⟨le_rfl, hr.le⟩ ⟨hr.le, le_rfl⟩ hr
  have he : (w.re : ℂ)+(w.im : ℂ)*I = w := by simp
  simpa only [H, ofReal_zero, zero_add, re_F_imaginary, he] using hlt

theorem re_F_neg {w : ℂ} (hw : ‖w‖ < 1) (hr : w.re < 0) : (F w).re < 0 := by
  have h := re_F_pos (w := -w) (by simpa using hw) (by simpa using neg_pos.mpr hr)
  simpa only [F_neg, neg_re, neg_pos] using h

theorem re_F_eq_zero {w : ℂ} (hr : w.re = 0) : (F w).re = 0 := by
  have he : w = (w.im : ℂ)*I := by apply Complex.ext <;> simp [hr]
  rw [he, re_F_imaginary]

end
end PlanarLens

end LowerBoundInline

end OAI
