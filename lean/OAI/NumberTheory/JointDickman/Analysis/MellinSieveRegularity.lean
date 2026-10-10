import OAI.NumberTheory.JointDickman.Analysis.MellinSieveProfile
import OAI.NumberTheory.JointDickman.Analysis.MellinPrefixBound
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Regularity of the positive Mellin sieve profile -/
namespace JointDickman
open Complex

noncomputable def mellinSieveFunction (N t x : ℝ) : ℂ :=
  (mellinSieveWeight N x : ℂ)*Complex.exp (((-Real.log x*t : ℝ) : ℂ)*I)

lemma mellin_power_phase {x : ℝ} (hx : 0 < x) (r t : ℝ) :
    (x : ℂ)^((r : ℂ)-(t : ℂ)*I) =
      ((x^r : ℝ) : ℂ)*Complex.exp (((-Real.log x*t : ℝ) : ℂ)*I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    ← Complex.ofReal_log hx.le]
  rw [show (Real.log x : ℂ)*((r : ℂ)-(t : ℂ)*I) =
    ((Real.log x*r : ℝ) : ℂ)+(((-Real.log x*t : ℝ) : ℂ)*I) by push_cast; ring,
    Complex.exp_add, ← Complex.ofReal_exp, Real.rpow_def_of_pos hx]

lemma mellinSieveFunction_left {N x : ℝ} (hN : 0 < N) (hx : 0 < x)
    (hxN : x ≤ N) (t : ℝ) :
    mellinSieveFunction N t x = (1/(N : ℂ))*(x : ℂ)^((1 : ℂ)-(t : ℂ)*I) := by
  rw [mellinSieveFunction, mellinSieveWeight_left hN hx hxN,
    (show (x : ℂ)^((1 : ℂ)-(t : ℂ)*I) = _ from
      by simpa only [Complex.ofReal_one] using mellin_power_phase hx 1 t), Real.rpow_one]
  push_cast
  ring

lemma mellinSieveFunction_right {N x : ℝ} (hN : 0 < N) (hxN : N ≤ x) (t : ℝ) :
    mellinSieveFunction N t x = (N : ℂ)^3*(x : ℂ)^((-3 : ℂ)-(t : ℂ)*I) := by
  have hx := hN.trans_le hxN
  rw [mellinSieveFunction, mellinSieveWeight_right hN hxN,
    show ((-3 : ℂ)-(t : ℂ)*I) = (((-3 : ℝ) : ℂ)-(t : ℂ)*I) by norm_num,
    mellin_power_phase hx, Real.rpow_neg hx.le]
  simp only [Real.rpow_ofNat, Complex.ofReal_inv, Complex.ofReal_pow]
  push_cast
  ring

lemma norm_mellin_exponent (r t : ℝ) :
    ‖(r : ℂ)-(t : ℂ)*I‖ ≤ |r|+|t| := by
  simpa only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] using
    norm_sub_le (r : ℂ) ((t : ℂ)*I)

lemma mellinSieveFunction_left_sub {N a b : ℝ} (hN : 0 < N)
    (ha : 0 < a) (hab : a ≤ b) (hbN : b ≤ N) (t : ℝ) :
    ‖mellinSieveFunction N t b-mellinSieveFunction N t a‖ ≤
      ((3+|t|)/N)*(b-a) := by
  let s : ℂ := 1-(t : ℂ)*I
  have hs : s.re = 1 := by simp [s]
  have hs0 : s ≠ 0 := by intro he; rw [he] at hs; simp at hs
  have hder (x : ℝ) (hx : x ∈ Set.Icc a b) :
      HasDerivAt (fun x : ℝ => (1/(N : ℂ))*(x : ℂ)^s)
        ((1/(N : ℂ))*(s*(x : ℂ)^(s-1))) x := by
    exact (hasDerivAt_ofReal_cpow_const (ha.trans_le hx.1).ne' hs0).const_mul _
  have hbound (x : ℝ) (hx : x ∈ Set.Icc a b) :
      ‖(1/(N : ℂ))*(s*(x : ℂ)^(s-1))‖ ≤ (3+|t|)/N := by
    rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos (ha.trans_le hx.1)]
    simp only [Complex.sub_re, hs, one_re, sub_self, Real.rpow_zero, mul_one,
      norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
    have hh := norm_mellin_exponent 1 t
    norm_num at hh
    dsimp [s]
    apply (show (1/N)*‖(1 : ℂ)-(t : ℂ)*I‖ = ‖(1 : ℂ)-(t : ℂ)*I‖/N by ring).trans_le
    exact div_le_div_of_nonneg_right (hh.trans (by linarith)) hN.le
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hder x hx).hasDerivWithinAt) hbound (convex_Icc a b)
    (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hh
  rw [mellinSieveFunction_left hN (ha.trans_le hab) hbN,
    mellinSieveFunction_left hN ha (hab.trans hbN)]
  exact hh

lemma mellinSieveFunction_right_sub {N a b : ℝ} (hN : 0 < N)
    (hNa : N ≤ a) (hab : a ≤ b) (t : ℝ) :
    ‖mellinSieveFunction N t b-mellinSieveFunction N t a‖ ≤
      ((3+|t|)/N)*(b-a) := by
  let s : ℂ := -3-(t : ℂ)*I
  have hs : s.re = -3 := by simp [s]
  have hs0 : s ≠ 0 := by intro he; rw [he] at hs; norm_num at hs
  have hder (x : ℝ) (hx : x ∈ Set.Icc a b) :
      HasDerivAt (fun x : ℝ => (N : ℂ)^3*(x : ℂ)^s)
        ((N : ℂ)^3*(s*(x : ℂ)^(s-1))) x := by
    exact (hasDerivAt_ofReal_cpow_const (hN.trans_le (hNa.trans hx.1)).ne' hs0).const_mul _
  have hbound (x : ℝ) (hx : x ∈ Set.Icc a b) :
      ‖(N : ℂ)^3*(s*(x : ℂ)^(s-1))‖ ≤ (3+|t|)/N := by
    have hxN : N ≤ x := hNa.trans hx.1
    have hx0 : 0 < x := hN.trans_le hxN
    rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [Complex.sub_re, hs, one_re, show (-3:ℝ)-1 = -4 by norm_num,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
    rw [Real.rpow_neg hx0.le, show (4:ℝ) = (4:ℕ) by norm_num, Real.rpow_natCast]
    have hh : ‖s‖ ≤ 3+|t| := by simpa [s] using norm_mellin_exponent (-3) t
    have hp : N^4 ≤ x^4 := pow_le_pow_left₀ hN.le hxN 4
    have hfrac : N^3*(x^4)⁻¹ ≤ 1/N := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (pow_pos hx0 4) hN]
      nlinarith
    calc
      _ = (N^3*(x^4)⁻¹)*‖s‖ := by ring
      _ ≤ (1/N)*(3+|t|) := mul_le_mul hfrac hh (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hder x hx).hasDerivWithinAt) hbound (convex_Icc a b)
    (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hh
  rw [mellinSieveFunction_right hN (hNa.trans hab), mellinSieveFunction_right hN hNa]
  exact hh

lemma norm_mellinSieveFunction (N t x : ℝ) :
    ‖mellinSieveFunction N t x‖ = |mellinSieveWeight N x| := by
  rw [mellinSieveFunction, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

lemma mellinSieveFunction_zero (N t : ℝ) : mellinSieveFunction N t 0 = 0 := by
  simp [mellinSieveFunction, mellinSieveWeight]

lemma norm_mellinSieveFunction_le {N x : ℝ} (hN : 0 < N) (hx : 0 ≤ x) (t : ℝ) :
    ‖mellinSieveFunction N t x‖ ≤ x/N := by
  rw [norm_mellinSieveFunction, abs_of_nonneg (mellinSieveWeight_nonneg hN.le hx)]
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp [mellinSieveWeight]
  by_cases hxN : x ≤ N
  · exact (mellinSieveWeight_left hN hx hxN).le
  · have hNx : N ≤ x := le_of_not_ge hxN
    rw [mellinSieveWeight_right hN hNx]
    have hr : N/x ≤ 1 := (div_le_one hx).mpr hNx
    exact (pow_le_one₀ (by positivity) hr).trans ((one_le_div hN).mpr hNx)

/-- The cusp at the profile's maximum does not affect its global
Lipschitz bound on the nonnegative half-line. -/
lemma mellinSieveFunction_sub {N a b : ℝ} (hN : 0 < N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (t : ℝ) :
    ‖mellinSieveFunction N t b-mellinSieveFunction N t a‖ ≤
      ((3+|t|)/N)*|b-a| := by
  suffices hh : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      ‖mellinSieveFunction N t b-mellinSieveFunction N t a‖ ≤
        ((3+|t|)/N)*(b-a) by
    rcases le_total a b with hab | hba
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hh a b ha hab
    · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hba)]
      exact hh b a hb hba
  intro a b ha hab
  rcases eq_or_lt_of_le ha with rfl | ha
  · rw [mellinSieveFunction_zero, sub_zero, sub_zero]
    apply (norm_mellinSieveFunction_le hN hab t).trans
    have hc : 1/N ≤ (3+|t|)/N :=
      div_le_div_of_nonneg_right (by linarith [abs_nonneg t]) hN.le
    simpa only [one_mul, div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right hc hab
  · by_cases hbN : b ≤ N
    · exact mellinSieveFunction_left_sub hN ha hab hbN t
    · by_cases hNa : N ≤ a
      · exact mellinSieveFunction_right_sub hN hNa hab t
      · have haN : a ≤ N := le_of_not_ge hNa
        have hNb : N ≤ b := le_of_not_ge hbN
        calc
          _ ≤ ‖mellinSieveFunction N t b-mellinSieveFunction N t N‖ +
              ‖mellinSieveFunction N t N-mellinSieveFunction N t a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ ((3+|t|)/N)*(b-N)+((3+|t|)/N)*(N-a) := add_le_add
            (mellinSieveFunction_right_sub hN le_rfl hNb t)
            (mellinSieveFunction_left_sub hN ha haN le_rfl t)
          _ = _ := by ring

lemma mellinSieveFunction_continuousOn {N : ℝ} (hN : 0 < N) (t : ℝ) :
    ContinuousOn (mellinSieveFunction N t) (Set.Ici 0) := by
  exact (LipschitzOnWith.of_dist_le' (fun a ha b hb => by
    simpa only [dist_eq_norm, Real.norm_eq_abs] using mellinSieveFunction_sub hN hb ha t)).continuousOn

end JointDickman

end OAI
