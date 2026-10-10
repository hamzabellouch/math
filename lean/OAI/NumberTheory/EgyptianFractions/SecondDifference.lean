import Mathlib

namespace OAI
open Set

namespace Problem337

/-- A second finite difference is a second derivative value times the squared
step. Only pointwise derivative data on the relevant closed interval is used. -/
theorem second_difference_eq_deriv (f f' f'' : ℝ → ℝ) (x h : ℝ) (hh : 0 < h)
    (hf : ∀ y ∈ Icc x (x + 2 * h), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc x (x + 2 * h), HasDerivAt f' (f'' y) y) :
    ∃ c ∈ Ioo x (x + 2 * h),
      f (x + 2 * h) - 2 * f (x + h) + f x = h ^ 2 * f'' c := by
  let g : ℝ → ℝ := fun y => f (y + h) - f y
  let g' : ℝ → ℝ := fun y => f' (y + h) - f' y
  have hg : ∀ y ∈ Icc x (x + h), HasDerivAt g (g' y) y := by
    intro y hy
    have hy1 : y ∈ Icc x (x + 2 * h) := ⟨hy.1, by linarith [hy.2]⟩
    have hy2 : y + h ∈ Icc x (x + 2 * h) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have htrans := (hf (y + h) hy2).comp_add_const y h
    exact htrans.fun_sub (hf y hy1)
  obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope g g' (by linarith : x < x + h)
    (fun y hy => (hg y hy).continuousAt.continuousWithinAt)
    (fun y hy => hg y ⟨hy.1.le, hy.2.le⟩)
  have hinterval : Icc c (c + h) ⊆ Icc x (x + 2 * h) := by
    intro y hy
    constructor <;> linarith [hc.1, hc.2, hy.1, hy.2]
  obtain ⟨d, hd, hdeq⟩ := exists_hasDerivAt_eq_slope f' f'' (by linarith : c < c + h)
    (fun y hy => (hf' y (hinterval hy)).continuousAt.continuousWithinAt)
    (fun y hy => hf' y (hinterval ⟨hy.1.le, hy.2.le⟩))
  refine ⟨d, ⟨by linarith [hc.1, hd.1], by linarith [hc.2, hd.2]⟩, ?_⟩
  have heq' : g (x + h) - g x = h * g' c := by
    have : x + h - x = h := by ring
    rw [this] at heq
    exact (eq_div_iff (ne_of_gt hh)).mp heq |> (fun H => by nlinarith [H])
  have hdeq' : f' (c + h) - f' c = h * f'' d := by
    have : c + h - c = h := by ring
    rw [this] at hdeq
    have := (eq_div_iff (ne_of_gt hh)).mp hdeq
    nlinarith
  dsimp [g, g'] at heq'
  have hx : x + h + h = x + 2 * h := by ring
  rw [hx, hdeq'] at heq'
  nlinarith

/-- Bounds for the second derivative give bounds for each second difference. -/
theorem second_difference_bounds (f f' f'' : ℝ → ℝ) (x h L U : ℝ) (hh : 0 < h)
    (hf : ∀ y ∈ Icc x (x + 2 * h), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc x (x + 2 * h), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Icc x (x + 2 * h), L ≤ f'' y ∧ f'' y ≤ U) :
    h ^ 2 * L ≤ f (x + 2 * h) - 2 * f (x + h) + f x ∧
      f (x + 2 * h) - 2 * f (x + h) + f x ≤ h ^ 2 * U := by
  obtain ⟨c, hc, heq⟩ := second_difference_eq_deriv f f' f'' x h hh hf hf'
  rw [heq]
  have hb := hbound c ⟨hc.1.le, hc.2.le⟩
  exact ⟨mul_le_mul_of_nonneg_left hb.1 (sq_nonneg h),
    mul_le_mul_of_nonneg_left hb.2 (sq_nonneg h)⟩

/-- Telescoping a two-sided bound for adjacent increments. -/
theorem discrete_increment_bounds (d : ℕ → ℝ) (a b : ℕ) (L U : ℝ)
    (hab : a ≤ b)
    (hstep : ∀ j ∈ Finset.Ico a b, L ≤ d (j + 1) - d j ∧ d (j + 1) - d j ≤ U) :
    L * ((b : ℝ) - a) ≤ d b - d a ∧ d b - d a ≤ U * ((b : ℝ) - a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hprev : ∀ j ∈ Finset.Ico a b, L ≤ d (j + 1) - d j ∧ d (j + 1) - d j ≤ U := by
      intro j hj
      exact hstep j (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hj).1,
        (Finset.mem_Ico.mp hj).2.trans (Nat.lt_succ_self b)⟩)
    have hlast := hstep b (Finset.mem_Ico.mpr ⟨hab, by omega⟩)
    have hprior := ih hprev
    push_cast
    constructor <;> nlinarith [hprior.1, hprior.2, hlast.1, hlast.2]

/-- Continuous second-derivative bounds imply the separation hypotheses for
sampled first differences used by the discrete second-derivative test. -/
theorem sampled_increment_bounds (f f' f'' : ℝ → ℝ) (a b : ℕ) (L U : ℝ)
    (hab : a ≤ b)
    (hf : ∀ y ∈ Icc (a : ℝ) ((b : ℝ) + 1), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc (a : ℝ) ((b : ℝ) + 1), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Icc (a : ℝ) ((b : ℝ) + 1), L ≤ f'' y ∧ f'' y ≤ U) :
    L * ((b : ℝ) - a) ≤
        (f ((b : ℝ) + 1) - f b) - (f ((a : ℝ) + 1) - f a) ∧
      (f ((b : ℝ) + 1) - f b) - (f ((a : ℝ) + 1) - f a) ≤ U * ((b : ℝ) - a) := by
  apply discrete_increment_bounds (fun n => f ((n : ℝ) + 1) - f n) a b L U hab
  intro n hn
  have hna : (a : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
  have hnb : (n : ℝ) + 1 ≤ b := by exact_mod_cast (Finset.mem_Ico.mp hn).2
  have hsub : Icc (n : ℝ) ((n : ℝ) + 2 * 1) ⊆ Icc (a : ℝ) ((b : ℝ) + 1) := by
    intro y hy
    constructor <;> linarith [hy.1, hy.2]
  have hh := second_difference_bounds f f' f'' (n : ℝ) 1 L U (by norm_num)
    (fun y hy => hf y (hsub hy)) (fun y hy => hf' y (hsub hy))
    (fun y hy => hbound y (hsub hy))
  norm_num only [one_pow, one_mul, mul_one] at hh
  push_cast
  have heq : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
  rw [heq]
  constructor <;> linarith [hh.1, hh.2]

/-- Darboux's theorem makes the sign of a nonvanishing second derivative
constant. Absolute derivative bounds therefore give one uniform signed strip. -/
theorem second_derivative_signed_bounds (f' f'' : ℝ → ℝ) (s : Set ℝ)
    (hs : Convex ℝ s) (L U : ℝ) (hL : 0 < L)
    (hf' : ∀ x ∈ s, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ s, L ≤ |f'' x| ∧ |f'' x| ≤ U) :
    (∀ x ∈ s, L ≤ f'' x ∧ f'' x ≤ U) ∨
      (∀ x ∈ s, -U ≤ f'' x ∧ f'' x ≤ -L) := by
  have hn : ∀ x ∈ s, f'' x ≠ 0 := by
    intro x hx heq
    have := (hbound x hx).1
    rw [heq, abs_zero] at this
    linarith
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne hs
      (fun x hx => (hf' x hx).hasDerivWithinAt) hn with hneg | hpos
  · right
    intro x hx
    have hb := hbound x hx
    rw [abs_of_neg (hneg x hx)] at hb
    constructor <;> linarith [hb.1, hb.2]
  · left
    intro x hx
    simpa only [abs_of_pos (hpos x hx)] using hbound x hx

/-- Positive lower absolute second-derivative bounds give separation of all
sampled first differences, whether the second derivative is positive or negative. -/
theorem sampled_increment_abs_bounds (f f' f'' : ℝ → ℝ) (a b : ℕ) (L U : ℝ)
    (hab : a ≤ b) (hL : 0 < L)
    (hf : ∀ y ∈ Icc (a : ℝ) ((b : ℝ) + 1), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc (a : ℝ) ((b : ℝ) + 1), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Icc (a : ℝ) ((b : ℝ) + 1), L ≤ |f'' y| ∧ |f'' y| ≤ U) :
    L * ((b : ℝ) - a) ≤
        |(f ((b : ℝ) + 1) - f b) - (f ((a : ℝ) + 1) - f a)| ∧
      |(f ((b : ℝ) + 1) - f b) - (f ((a : ℝ) + 1) - f a)| ≤
        U * ((b : ℝ) - a) := by
  have hba : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
  rcases second_derivative_signed_bounds f' f'' _ (convex_Icc _ _) L U hL hf' hbound
      with hpos | hneg
  · have hb := sampled_increment_bounds f f' f'' a b L U hab hf hf' hpos
    rw [abs_of_nonneg (mul_nonneg hL.le hba |>.trans hb.1)]
    exact hb
  · have hb := sampled_increment_bounds f f' f'' a b (-U) (-L) hab hf hf' hneg
    have hn : (f ((b : ℝ) + 1) - f b) - (f ((a : ℝ) + 1) - f a) ≤ 0 := by
      exact hb.2.trans (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL.le) hba)
    rw [abs_of_nonpos hn]
    constructor <;> nlinarith [hb.1, hb.2]

/-- Sampled first differences are monotone in one direction under a positive
absolute lower bound for the second derivative. -/
theorem sampled_increment_strictMono_or_strictAnti (f f' f'' : ℝ → ℝ)
    (a b : ℕ) (L U : ℝ) (hL : 0 < L)
    (hf : ∀ y ∈ Icc (a : ℝ) ((b : ℝ) + 1), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc (a : ℝ) ((b : ℝ) + 1), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Icc (a : ℝ) ((b : ℝ) + 1), L ≤ |f'' y| ∧ |f'' y| ≤ U) :
    StrictMonoOn (fun n : ℕ => f ((n : ℝ) + 1) - f n) (Icc a b) ∨
      StrictAntiOn (fun n : ℕ => f ((n : ℝ) + 1) - f n) (Icc a b) := by
  have hsub : ∀ i ∈ Icc a b, ∀ j ∈ Icc a b,
      Icc (i : ℝ) ((j : ℝ) + 1) ⊆ Icc (a : ℝ) ((b : ℝ) + 1) := by
    intro i hi j hj y hy
    have hai : (a : ℝ) ≤ i := by exact_mod_cast hi.1
    have hjb : (j : ℝ) ≤ b := by exact_mod_cast hj.2
    exact ⟨hai.trans hy.1, by linarith [hy.2]⟩
  rcases second_derivative_signed_bounds f' f'' _ (convex_Icc _ _) L U hL hf' hbound
      with hpos | hneg
  · left
    intro i hi j hj hij
    have hb := sampled_increment_bounds f f' f'' i j L U hij.le
      (fun y hy => hf y (hsub i hi j hj hy))
      (fun y hy => hf' y (hsub i hi j hj hy))
      (fun y hy => hpos y (hsub i hi j hj hy))
    have hr : 0 < (j : ℝ) - i := sub_pos.mpr (by exact_mod_cast hij)
    have := mul_pos hL hr
    linarith [hb.1]
  · right
    intro i hi j hj hij
    have hb := sampled_increment_bounds f f' f'' i j (-U) (-L) hij.le
      (fun y hy => hf y (hsub i hi j hj hy))
      (fun y hy => hf' y (hsub i hi j hj hy))
      (fun y hy => hneg y (hsub i hi j hj hy))
    have hr : 0 < (j : ℝ) - i := sub_pos.mpr (by exact_mod_cast hij)
    have := mul_pos hL hr
    nlinarith [hb.2]

end Problem337

end OAI
