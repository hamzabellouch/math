import OAI.NumberTheory.Ostmann.ZeroDensity.RegularizedZeta
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterLocalZeroCount

namespace OAI

/-! # Polynomial bounds for the pole-removed zeta function on right-half-plane disks -/

namespace Ostmann

open Complex Metric Set

theorem riemannZeta_lower_re_two (s : ℂ) (hs : s.re = 2) :
    1 / 3 ≤ ‖riemannZeta s‖ := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.moebius n : ℂ)
  have hf (n : ℕ) (_hn : n ≠ 0) : ‖f n‖ ≤ 1 := by
    dsimp [f]
    norm_cast
    exact ArithmeticFunction.abs_moebius_le_one
  have hb := lSeries_norm_bound_re_two f hf s hs
  have he : riemannZeta s * LSeries f s = 1 := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta (by rw [hs]; norm_num)]
    exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius (by rw [hs]; norm_num)
  have hn := congrArg norm he
  rw [norm_mul, norm_one] at hn
  have hpi : Real.pi ^ 2 / 6 ≤ 3 := by
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hm := mul_le_mul_of_nonneg_left (hb.trans hpi) (norm_nonneg (riemannZeta s))
  rw [hn] at hm
  linarith

theorem regularizedZeta_lower_center (t : ℝ) :
    1 / 3 ≤ ‖regularizedZeta (characterZeroCenter t)‖ := by
  have hne : characterZeroCenter t ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
  have hlo := riemannZeta_lower_re_two (characterZeroCenter t) (characterZeroCenter_re t)
  have hnorm : 1 ≤ ‖characterZeroCenter t - 1‖ := by
    have hh := Complex.re_le_norm (characterZeroCenter t - 1)
    norm_num only [Complex.sub_re, characterZeroCenter_re, Complex.one_re, Nat.reduceSub,
      show (2 : ℝ) - 1 = 1 by norm_num] at hh
    exact hh
  rw [regularizedZeta_eq _ hne, norm_mul]
  nlinarith [norm_nonneg (riemannZeta (characterZeroCenter t))]

theorem regularizedZeta_disk_bound (t : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (characterZeroCenter t) (7 / 4 : ℝ)) :
    ‖regularizedZeta z‖ ≤ 32 * (|t| + 2) ^ 2 := by
  have hbound := regularizedZeta_norm_bound z (character_disk_re t z hz)
  have hn := character_disk_norm t z hz
  have hsub : ‖z - 1‖ ≤ |t| + 5 := by
    have hh := norm_sub_le z 1
    rw [norm_one] at hh
    linarith
  have hprod : ‖z - 1‖ * ‖z‖ ≤ (|t| + 5) * (|t| + 4) :=
    mul_le_mul hsub hn (norm_nonneg _) (by positivity)
  nlinarith [abs_nonneg t, sq_nonneg t]

end Ostmann

end OAI
