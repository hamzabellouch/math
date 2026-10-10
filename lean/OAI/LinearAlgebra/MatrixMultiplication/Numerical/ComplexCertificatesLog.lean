import OAI.LinearAlgebra.MatrixMultiplication.Numerical.ComplexRationalLogCertificate
import OAI.LinearAlgebra.MatrixMultiplication.Numerical.ComplexLogThreeCertificate

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

namespace MatrixMultiplication.ComplexCertificates

open MatrixMultiplication.Foundation.RationalLogCertificate

theorem log_bounds_of_reduction {x : ℚ} (d : ReducedArgument x) (lo hi : ℚ)
    (hl : lo < reducedApprox d - (1 + |(d.exponent : ℚ)|) / 2 ^ 120)
    (hu : reducedApprox d + (1 + |(d.exponent : ℚ)|) / 2 ^ 120 < hi) :
    (lo : ℝ) < Real.log (x : ℝ) ∧ Real.log (x : ℝ) < (hi : ℝ) := by
  have herror := abs_le.mp (reduced_log_error d)
  have hl' : (lo : ℝ) < (reducedApprox d : ℝ) -
      (1 + |(d.exponent : ℝ)|) / 2 ^ 120 := by exact_mod_cast hl
  have hu' : (reducedApprox d : ℝ) +
      (1 + |(d.exponent : ℝ)|) / 2 ^ 120 < (hi : ℝ) := by exact_mod_cast hu
  constructor <;> linarith

def reduceTwo : ReducedArgument (2 : ℚ) where
  exponent := 0
  mantissa := 2
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

theorem log_two_bounds :
    (34657 : ℝ) / 50000 < Real.log 2 ∧ Real.log 2 < (17329 : ℝ) / 25000 := by
  have h := log_bounds_of_reduction reduceTwo (34657 / 50000) (17329 / 25000)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h

def reduceThree : ReducedArgument (3 : ℚ) where
  exponent := 1
  mantissa := 3 / 2
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

theorem log_three_lower : (549 : ℝ) / 500 < Real.log 3 := by
  have h := log_bounds_of_reduction reduceThree (549 / 500) (10987 / 10000)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h.1

theorem log_three_upper : Real.log 3 < (10987 : ℝ) / 10000 := by
  have h := MatrixMultiplication.Foundation.log_three_upper
  norm_num at h ⊢
  linarith

def reduceNineteen : ReducedArgument (19 : ℚ) where
  exponent := 4
  mantissa := 19 / 16
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

theorem log_nineteen_bounds :
    (7361 : ℝ) / 2500 < Real.log 19 ∧ Real.log 19 < (5889 : ℝ) / 2000 := by
  have h := log_bounds_of_reduction reduceNineteen (7361 / 2500) (5889 / 2000)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h

def reduceCurveLo : ReducedArgument (246439 / 5000 : ℚ) where
  exponent := 5
  mantissa := 246439 / 160000
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

def reduceCurveHi : ReducedArgument (49289 / 1000 : ℚ) where
  exponent := 5
  mantissa := 49289 / 32000
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

theorem log_curve_lower :
    (77953 : ℝ) / 20000 < Real.log ((246439 : ℝ) / 5000) := by
  have h := log_bounds_of_reduction reduceCurveLo (77953 / 20000) (97443 / 25000)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h.1

theorem log_curve_upper :
    Real.log ((49289 : ℝ) / 1000) < (97443 : ℝ) / 25000 := by
  have h := log_bounds_of_reduction reduceCurveHi (77953 / 20000) (97443 / 25000)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h.2

def reduceTen : ReducedArgument (10 : ℚ) where
  exponent := 3
  mantissa := 5 / 4
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

theorem log_ten_lower : (921 : ℝ) / 400 < Real.log 10 := by
  have h := log_bounds_of_reduction reduceTen (921 / 400) (2303 / 1000)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h.1

def reduceSquareMantissa : ReducedArgument (59 / 20 : ℚ) where
  exponent := 1
  mantissa := 59 / 40
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

theorem log_square_mantissa_lower :
    (10817 : ℝ) / 10000 < Real.log ((59 : ℝ) / 20) := by
  have h := log_bounds_of_reduction reduceSquareMantissa (10817 / 10000) (541 / 500)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h.1

def reduceNineSevenths : ReducedArgument (9 / 7 : ℚ) where
  exponent := 0
  mantissa := 9 / 7
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

theorem log_nine_sevenths_bounds :
    (1 : ℝ) / 4 < Real.log (9 / 7 : ℝ) ∧ Real.log (9 / 7 : ℝ) < (63 : ℝ) / 250 := by
  have h := log_bounds_of_reduction reduceNineSevenths (1 / 4) (63 / 250)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h

def reduceExpLo48 : ReducedArgument (701 / 1000 : ℚ) where
  exponent := -1
  mantissa := 701 / 500
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

theorem exp_neg_354_lower : (701 : ℝ) / 1000 < Real.exp (-(177 / 500 : ℝ)) := by
  have h := log_bounds_of_reduction reduceExpLo48 (-356 / 1000) (-177 / 500)
    (by decide +kernel) (by decide +kernel)
  have hh : Real.log (701 / 1000 : ℝ) < -(177 / 500 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, neg_div] using h.2
  exact (Real.log_lt_iff_lt_exp (by norm_num)).1 hh

def reduceExpHi48 : ReducedArgument (707 / 1000 : ℚ) where
  exponent := -1
  mantissa := 707 / 500
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

theorem exp_neg_348_upper : Real.exp (-(87 / 250 : ℝ)) < (707 : ℝ) / 1000 := by
  have h := log_bounds_of_reduction reduceExpHi48 (-87 / 250) (-346 / 1000)
    (by decide +kernel) (by decide +kernel)
  have hh : -(87 / 250 : ℝ) < Real.log (707 / 1000 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, neg_div] using h.1
  exact (Real.lt_log_iff_exp_lt (by norm_num)).1 hh

def reduceExpLo288 : ReducedArgument (169 / 400 : ℚ) where
  exponent := -2
  mantissa := 169 / 100
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

theorem exp_neg_86_lower : (169 : ℝ) / 400 < Real.exp (-(43 / 50 : ℝ)) := by
  have h := log_bounds_of_reduction reduceExpLo288 (-863 / 1000) (-43 / 50)
    (by decide +kernel) (by decide +kernel)
  have hh : Real.log (169 / 400 : ℝ) < -(43 / 50 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, neg_div] using h.2
  exact (Real.log_lt_iff_lt_exp (by norm_num)).1 hh

def reduceZ48Lo : ReducedArgument (((1 + 701 / 1000) ^ 2 - 1) : ℚ) where
  exponent := 0
  mantissa := (1 + 701 / 1000) ^ 2 - 1
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

def reduceZ48Hi : ReducedArgument (((1 + 707 / 1000) ^ 2 - 1) : ℚ) where
  exponent := 0
  mantissa := (1 + 707 / 1000) ^ 2 - 1
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

theorem log_z48_lower :
    (127 : ℝ) / 200 < Real.log ((1 + (701 / 1000 : ℝ)) ^ 2 - 1) := by
  have h := log_bounds_of_reduction reduceZ48Lo (127 / 200) (651 / 1000)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h.1

theorem log_z48_upper :
    Real.log ((1 + (707 / 1000 : ℝ)) ^ 2 - 1) < (651 : ℝ) / 1000 := by
  have h := log_bounds_of_reduction reduceZ48Hi (127 / 200) (651 / 1000)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h.2

def reduceZ288Lo : ReducedArgument (((1 + 169 / 400) ^ 3 - 1) : ℚ) where
  exponent := 0
  mantissa := (1 + 169 / 400) ^ 3 - 1
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

theorem log_z288_lower :
    (157 : ℝ) / 250 < Real.log ((1 + (169 / 400 : ℝ)) ^ 3 - 1) := by
  have h := log_bounds_of_reduction reduceZ288Lo (157 / 250) (16 / 25)
    (by decide +kernel) (by decide +kernel)
  norm_num at h ⊢
  exact h.1

end MatrixMultiplication.ComplexCertificates

end OAI
