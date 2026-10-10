import OAI.NumberTheory.JointDickman.Analysis.MellinPrefixBound

namespace OAI

/-! # Bounded-frequency control on subintervals with comparable endpoints -/
namespace JointDickman
open Finset Complex

theorem angularMellinPolynomial_le_of_prefix_interval (a : ℕ → ℂ) {X Y T D t : ℝ}
    (hX : 0 < X) (hXY : X ≤ Y) (hY : Y ≤ 4*X) (hT : 0 ≤ T) (hD : 0 ≤ D) (ht : |t| ≤ T)
    (hprefix : ∀ u ∈ Set.Icc X Y, ‖∑ n ∈ Icc 0 ⌊u⌋₊, a n‖ ≤ D) :
    ‖angularMellinPolynomial (Ioc ⌊X⌋₊ ⌊Y⌋₊) a t‖ ≤
      (5 + 3 * T) * D / X := by
  let s : ℂ := 1 + (t : ℂ) * I
  let φ : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  let φ' : ℝ → ℂ := fun u => (-s) * (u : ℂ) ^ (-(s + 1))
  have hs : s.re = 1 := by simp [s]
  have hs0 : s ≠ 0 := by intro hh; rw [hh] at hs; simp at hs
  have hsnorm : ‖s‖ ≤ 1 + T := by
    have hh := norm_add_le (1 : ℂ) ((t : ℂ) * I)
    simp only [norm_one, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hh
    exact hh.trans (by linarith)
  have hd (u : ℝ) (hu : u ∈ Set.Icc X Y) : HasDerivAt φ (φ' u) u := by
    have hu0 : 0 < u := hX.trans_le hu.1
    dsimp [φ, φ']
    rw [show -(s + 1) = -s - 1 by ring]
    exact hasDerivAt_ofReal_cpow_const hu0.ne' (neg_ne_zero.mpr hs0)
  have hc : ContinuousOn φ' (Set.Icc X Y) := by
    intro u hu
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
      (.inr (hX.trans_le hu.1).ne'))).continuousWithinAt
  have hv (u : ℝ) (hu : u ∈ Set.Icc X Y) : ‖φ u‖ ≤ 1 / X := by
    have hu0 : 0 < u := hX.trans_le hu.1
    dsimp [φ]
    rw [norm_cpow_eq_rpow_re_of_pos hu0, neg_re, hs]
    simpa only [Real.rpow_neg_one, one_div] using one_div_le_one_div_of_le hX hu.1
  have hv' (u : ℝ) (hu : u ∈ Set.Icc X Y) : ‖φ' u‖ ≤ (1 + T) / X ^ 2 := by
    have hu0 : 0 < u := hX.trans_le hu.1
    have hp : X ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hX.le hu.1 2
    dsimp [φ']
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hu0]
    have he : (-(s + 1)).re = (-2 : ℝ) := by norm_num [hs]
    rw [he]
    have hpow : u ^ (-2 : ℝ) = 1 / u ^ 2 := by
      rw [Real.rpow_neg hu0.le, Real.rpow_two, one_div]
    rw [hpow, one_div, ← div_eq_mul_inv]
    exact (div_le_div_of_nonneg_right hsnorm (sq_nonneg u)).trans
      (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hX) hp)
  have hb := complex_partial_summation_bound a φ φ' hX.le hXY hD
    (show 0 ≤ 1 / X by positivity) (show 0 ≤ (1 + T) / X ^ 2 by positivity)
    hd hc hv hv' hprefix
  rw [angularMellinPolynomial_cpow _ _ (by
    intro n hn
    exact (Nat.zero_le ⌊X⌋₊).trans_lt (mem_Ioc.mp hn).1)]
  change ‖∑ n ∈ Ioc ⌊X⌋₊ ⌊Y⌋₊, φ n * a n‖ ≤ _
  apply hb.trans
  calc
    _ ≤ D*(2*(1/X)+(1+T)/X^2*(4*X-X)) := by gcongr
    _ = _ := by field_simp; ring

end JointDickman

end OAI
