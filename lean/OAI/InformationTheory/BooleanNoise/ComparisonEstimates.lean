import OAI.InformationTheory.BooleanNoise.EntropyScalars
import OAI.InformationTheory.BooleanNoise.CurvatureCertificates
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

def comparisonC (u : ℝ) : ℝ :=
  100 / 81 + Real.log (9 / 10) - Real.log u

def comparisonBracket (u : ℝ) : ℝ :=
  (1 + u ^ 2 / 3) * comparisonC u - 1 / 3

theorem comparisonC_eq_log_div {u : ℝ} (hu : 0 < u) :
    comparisonC u = 100 / 81 + Real.log ((9 / 10) / u) := by
  rw [Real.log_div (by norm_num : (9 / 10 : ℝ) ≠ 0) hu.ne']
  unfold comparisonC
  ring

theorem comparisonC_lt_eleven_fourths {u : ℝ} (hu : (1 / 5 : ℝ) ≤ u) :
    comparisonC u < 11 / 4 := by
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 5) hu
  have hbase : Real.log (9 / 10 : ℝ) - Real.log (1 / 5 : ℝ) =
      Real.log (9 / 2 : ℝ) := by
    rw [← Real.log_div (by norm_num : (9 / 10 : ℝ) ≠ 0)
      (by norm_num : (1 / 5 : ℝ) ≠ 0)]
    norm_num
  have hnum := log_nine_halves_lt_151_div_100
  unfold comparisonC
  linarith

theorem hasDerivAt_comparisonC {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt comparisonC (-u⁻¹) u := by
  exact (Real.hasDerivAt_log hu).const_sub (100 / 81 + Real.log (9 / 10 : ℝ))

theorem hasDerivAt_comparisonBracket {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt comparisonBracket
      (u * (2 * comparisonC u - 1) / 3 - 1 / u) u := by
  have hp : HasDerivAt (fun v : ℝ => 1 + v ^ 2 / 3) (2 * u / 3) u := by
    convert! (((hasDerivAt_id u).pow 2).div_const 3).const_add 1 using 1
    simp
  convert! (hp.mul (hasDerivAt_comparisonC hu)).sub_const (1 / 3) using 1
  field_simp
  ring

theorem comparisonBracket_derivative_neg {u : ℝ}
    (hu0 : (1 / 5 : ℝ) ≤ u) (hu1 : u ≤ (5 / 8 : ℝ)) :
    u * (2 * comparisonC u - 1) / 3 - 1 / u < 0 := by
  have hu : 0 < u := by linarith
  have hC := comparisonC_lt_eleven_fourths hu0
  have hu2 : u ^ 2 ≤ (5 / 8 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (5 / 8 : ℝ) - u by linarith)
      (show 0 ≤ (5 / 8 : ℝ) + u by linarith)]
  have hmul : u ^ 2 * (2 * comparisonC u - 1) ≤ (9 / 2 : ℝ) * u ^ 2 := by
    have := mul_le_mul_of_nonneg_left (show 2 * comparisonC u - 1 ≤ (9 / 2 : ℝ) by
      linarith) (sq_nonneg u)
    nlinarith
  apply (mul_lt_mul_iff_left₀ hu).mp
  have heq : (u * (2 * comparisonC u - 1) / 3 - 1 / u) * u =
      u ^ 2 * (2 * comparisonC u - 1) / 3 - 1 := by
    field_simp
  rw [heq, zero_mul]
  nlinarith

theorem comparisonBracket_antitone :
    AntitoneOn comparisonBracket (Icc (1 / 5 : ℝ) (5 / 8)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro u hu
    exact (hasDerivAt_comparisonBracket (by linarith [hu.1])).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : u ∈ Icc (1 / 5 : ℝ) (5 / 8) := interior_subset hu
    exact (hasDerivAt_comparisonBracket (by linarith [hu'.1])).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' : u ∈ Icc (1 / 5 : ℝ) (5 / 8) := interior_subset hu
    rw [(hasDerivAt_comparisonBracket (by linarith [hu'.1])).deriv]
    exact (comparisonBracket_derivative_neg hu'.1 hu'.2).le

theorem comparisonC_middle_bound {u : ℝ}
    (hu0 : (1 / 5 : ℝ) ≤ u) (hu1 : u ≤ (5 / 8 : ℝ)) :
    (1 + u ^ 2 / 3) * comparisonC u - 1 / 3 ≤ (5 / 2 : ℝ) := by
  have hanti := comparisonBracket_antitone
    (show (1 / 5 : ℝ) ∈ Icc (1 / 5 : ℝ) (5 / 8) by constructor <;> norm_num)
    (show u ∈ Icc (1 / 5 : ℝ) (5 / 8) from ⟨hu0, hu1⟩) hu0
  have hbase : comparisonBracket (1 / 5 : ℝ) < (5 / 2 : ℝ) := by
    have hC := comparisonC_lt_eleven_fourths (show (1 / 5 : ℝ) ≤ 1 / 5 by norm_num)
    unfold comparisonBracket
    norm_num
    linarith
  exact hanti.trans hbase.le

theorem comparisonC_integral_bracket_nonneg {u : ℝ}
    (hu : 0 < u) (hu9 : u ≤ (9 / 10 : ℝ)) :
    0 ≤ 1 - u ^ 2 * comparisonC u := by
  have hlog := Real.log_le_sub_one_of_pos
    (div_pos (by norm_num : (0 : ℝ) < 9 / 10) hu)
  have hC : comparisonC u ≤ 100 / 81 + (9 / 10) / u - 1 := by
    rw [comparisonC_eq_log_div hu]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hC (sq_nonneg u)
  have heq : u ^ 2 * (100 / 81 + (9 / 10) / u - 1) =
      (19 / 81 : ℝ) * u ^ 2 + (9 / 10 : ℝ) * u := by
    field_simp
    ring
  rw [heq] at hmul
  have hu2 : u ^ 2 ≤ (9 / 10 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (9 / 10 : ℝ) - u by linarith)
      (show 0 ≤ (9 / 10 : ℝ) + u by linarith)]
  nlinarith

theorem comparison_large_regime (m u B P S v : ℝ)
    (hB0 : 0 ≤ B) (hB : B ≤ m ^ 2 * (ell - 1 / 2))
    (hP : u ^ 2 / 2 ≤ P)
    (hS : S ≤ (1 - m ^ 2) * P + B * (1 - v))
    (hu : (5 / 8 : ℝ) ≤ u) (hv : 0 ≤ v) : S ≤ P := by
  have hlevel : ell - 1 / 2 ≤ P := by
    have hell := ell_lt_347_div_500
    nlinarith [sq_nonneg (u - 5 / 8)]
  have hcorrection : B * (1 - v) ≤ m ^ 2 * P := by
    calc
      B * (1 - v) ≤ B := by nlinarith [mul_nonneg hB0 hv]
      _ ≤ m ^ 2 * (ell - 1 / 2) := hB
      _ ≤ m ^ 2 * P := mul_le_mul_of_nonneg_left hlevel (sq_nonneg m)
  nlinarith

theorem comparison_middle_regime (m u B P S v : ℝ)
    (hB0 : 0 ≤ B) (hB : B ≤ m ^ 2 * (ell - 1 / 2))
    (hP : u ^ 2 / 2 ≤ P)
    (hS : S ≤ (1 - m ^ 2) * P + B * (1 - v))
    (hv : 1 - v ≤ (5 / 2 : ℝ) * u ^ 2) : S ≤ P := by
  have hell : (ell - 1 / 2) * (5 / 2 : ℝ) ≤ 1 / 2 := by
    have h := ell_lt_347_div_500
    linarith
  have hcorrection : B * (1 - v) ≤ m ^ 2 * P := by
    calc
      B * (1 - v) ≤ B * ((5 / 2 : ℝ) * u ^ 2) :=
        mul_le_mul_of_nonneg_left hv hB0
      _ ≤ (m ^ 2 * (ell - 1 / 2)) * ((5 / 2 : ℝ) * u ^ 2) :=
        mul_le_mul_of_nonneg_right hB (by positivity)
      _ ≤ m ^ 2 * (u ^ 2 / 2) := by
        have h := mul_le_mul_of_nonneg_left hell
          (mul_nonneg (sq_nonneg m) (sq_nonneg u))
        nlinarith
      _ ≤ m ^ 2 * P := mul_le_mul_of_nonneg_left hP (sq_nonneg m)
  nlinarith

end LeanBlast.CourtadeKumar

end

end OAI
