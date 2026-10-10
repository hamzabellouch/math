import OAI.InformationTheory.BooleanNoise.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

def bernsteinSum (d : ℕ) (B : Fin (d + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ i, B i * (d.choose i.val : ℝ) * t ^ i.val * (1 - t) ^ (d - i.val)

theorem bernsteinSum_pos (d : ℕ) (B : Fin (d + 1) → ℝ)
    (hB : ∀ i, 0 < B i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < bernsteinSum d B t := by
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  unfold bernsteinSum
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (hB i).le (Nat.cast_nonneg _)) (pow_nonneg ht0 _))
      (pow_nonneg h1t _)
  · by_cases hlt : t < 1
    · refine ⟨⟨0, Nat.zero_lt_succ d⟩, Finset.mem_univ _, ?_⟩
      simpa only [Fin.val_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero,
        mul_one, Nat.sub_zero] using
        mul_pos (hB ⟨0, Nat.zero_lt_succ d⟩) (pow_pos (sub_pos.mpr hlt) d)
    · have ht : t = 1 := le_antisymm ht1 (le_of_not_gt hlt)
      refine ⟨⟨d, Nat.lt_succ_self d⟩, Finset.mem_univ _, ?_⟩
      simpa [ht] using hB ⟨d, Nat.lt_succ_self d⟩

def curvatureT (z : ℝ) : ℝ :=
  1 + z / 3 + z ^ 2 / 5 + z ^ 3 / 7 + z ^ 4 / 9 + z ^ 5 / 11

def curvatureP (z : ℝ) : ℝ :=
  347 / 500 - z / 2 - z ^ 2 / 12 - z ^ 3 / 30 - z ^ 4 / 56 - z ^ 5 / 90

def curvatureN (z : ℝ) : ℝ :=
  (1 - z) * (4 / 3 + (8 / 15) * z + (12 / 35) * z ^ 2 +
    (16 / 63) * z ^ 3 + (20 / 99) * z ^ 4) + (24 / 143) * z ^ 5

def curvaturePolynomial (z : ℝ) : ℝ :=
  2 * (1 - z) ^ 3 * curvatureT z ^ 3 - 3 * curvatureP z ^ 2 * curvatureN z

private def curvatureBernstein : Fin 19 → ℝ :=
  ![(4591 / 62500 : ℝ),
    (49876 / 703125 : ℝ),
    (616620509 / 9036562500 : ℝ),
    (425343109 / 6506325000 : ℝ),
    (1239780551 / 19880437500 : ℝ),
    (8677345901149 / 146538704812500 : ℝ),
    (243668974553 / 4355288437500 : ℝ),
    (9012669336346771 / 171450284630625000 : ℝ),
    (1633213857973883 / 33281525840062500 : ℝ),
    (270017981574109469 / 5940752362451156250 : ℝ),
    (49027630438590434159 / 1176268967765328937500 : ℝ),
    (363078011510202773129 / 9624018827170873125000 : ℝ),
    (10171907529149910232987 / 303156593055882503437500 : ℝ),
    (4117638512237582389 / 141331745014397437500 : ℝ),
    (29341211329970780039 / 1199300807693601112500 : ℝ),
    (7749647417493214337891 / 395769266538888367125000 : ℝ),
    (14423931694547701552427 / 989423166347220917812500 : ℝ),
    (140069602865401114033 / 14550340681576778203125 : ℝ),
    (2753371080520712929 / 554298692631496312500 : ℝ)]

private theorem curvatureBernstein_pos (i : Fin 19) : 0 < curvatureBernstein i := by
  fin_cases i <;> norm_num [curvatureBernstein]

theorem curvaturePolynomial_bernstein (t : ℝ) :
    curvaturePolynomial ((2 / 3) * t) = bernsteinSum 18 curvatureBernstein t := by
  simp only [bernsteinSum, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  norm_num [curvatureBernstein, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
  unfold curvaturePolynomial curvatureT curvatureP curvatureN
  ring

theorem curvatureCertificate_pos {z : ℝ} (hz0 : 0 ≤ z) (hz2 : z ≤ 2 / 3) :
    0 < curvaturePolynomial z := by
  have ht0 : 0 ≤ (3 / 2 : ℝ) * z := by positivity
  have ht1 : (3 / 2 : ℝ) * z ≤ 1 := by linarith
  have h := bernsteinSum_pos 18 curvatureBernstein curvatureBernstein_pos ht0 ht1
  rw [← curvaturePolynomial_bernstein] at h
  have he : (2 / 3 : ℝ) * ((3 / 2) * z) = z := by ring
  simpa only [he] using h

def lambdaPolynomial (b : ℝ) : ℝ :=
  4 - (5 / 2) * b - 5 * b ^ 2 - (7 / 4) * b ^ 3 + (56 / 15) * b ^ 4 +
    b ^ 5 + (15 / 14) * b ^ 6 + (3 / 8) * b ^ 7 + (8 / 15) * b ^ 8

private def lambdaBernsteinLow : Fin 9 → ℝ :=
  ![4,
    (241 / 64 : ℝ),
    (1537 / 448 : ℝ),
    (42755 / 14336 : ℝ),
    (217187 / 89600 : ℝ),
    (510487 / 286720 : ℝ),
    (8901163 / 8028160 : ℝ),
    (19161827 / 36700160 : ℝ),
    (1316227 / 4587520 : ℝ)]

private def lambdaBernsteinHigh : Fin 9 → ℝ :=
  ![(1316227 / 4587520 : ℝ),
    (7652479 / 36700160 : ℝ),
    (5432143 / 32112640 : ℝ),
    (2869523 / 16056320 : ℝ),
    (3747241 / 15052800 : ℝ),
    (1185781 / 3010560 : ℝ),
    (79071 / 125440 : ℝ),
    (5261 / 5376 : ℝ),
    (1229 / 840 : ℝ)]

private theorem lambdaBernsteinLow_pos (i : Fin 9) : 0 < lambdaBernsteinLow i := by
  fin_cases i <;> norm_num [lambdaBernsteinLow]

private theorem lambdaBernsteinHigh_pos (i : Fin 9) : 0 < lambdaBernsteinHigh i := by
  fin_cases i <;> norm_num [lambdaBernsteinHigh]

theorem lambdaPolynomial_bernstein_low (t : ℝ) :
    lambdaPolynomial ((3 / 4) * t) = bernsteinSum 8 lambdaBernsteinLow t := by
  unfold bernsteinSum
  simp_rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [lambdaPolynomial, lambdaBernsteinLow, Fin.sum_univ_succ,
    Nat.descFactorial, Nat.factorial]
  ring

theorem lambdaPolynomial_bernstein_high (t : ℝ) :
    lambdaPolynomial (3 / 4 + (1 / 4) * t) = bernsteinSum 8 lambdaBernsteinHigh t := by
  unfold bernsteinSum
  simp_rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [lambdaPolynomial, lambdaBernsteinHigh, Fin.sum_univ_succ,
    Nat.descFactorial, Nat.factorial]
  ring

theorem lambdaCertificate_pos {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 < lambdaPolynomial b := by
  by_cases hb : b ≤ 3 / 4
  · have ht0 : 0 ≤ (4 / 3 : ℝ) * b := by positivity
    have ht1 : (4 / 3 : ℝ) * b ≤ 1 := by linarith
    have h := bernsteinSum_pos 8 lambdaBernsteinLow lambdaBernsteinLow_pos ht0 ht1
    rw [← lambdaPolynomial_bernstein_low] at h
    have he : (3 / 4 : ℝ) * ((4 / 3) * b) = b := by ring
    simpa only [he] using h
  · have ht0 : 0 ≤ 4 * b - 3 := by linarith
    have ht1 : 4 * b - 3 ≤ 1 := by linarith
    have h := bernsteinSum_pos 8 lambdaBernsteinHigh lambdaBernsteinHigh_pos ht0 ht1
    rw [← lambdaPolynomial_bernstein_high] at h
    have he : (3 / 4 : ℝ) + (1 / 4) * (4 * b - 3) = b := by ring
    simpa only [he] using h

theorem two_lt_exp_347_div_500 : (2 : ℝ) < Real.exp (347 / 500) := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 347 / 500) 5)
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem ell_lt_347_div_500 : ell < 347 / 500 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mpr two_lt_exp_347_div_500

theorem nine_lt_exp_eleven_fifths : (9 : ℝ) < Real.exp (11 / 5) := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 5) 8)
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem nineteen_lt_exp_three : (19 : ℝ) < Real.exp 3 := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 7)
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_nineteen_lt_three : Real.log 19 < 3 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 19)).mpr nineteen_lt_exp_three

theorem nine_halves_lt_exp_151_div_100 : (9 / 2 : ℝ) < Real.exp (151 / 100) := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 151 / 100) 6)
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_nine_halves_lt_151_div_100 : Real.log (9 / 2) < 151 / 100 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 9 / 2)).mpr nine_halves_lt_exp_151_div_100

def smallCurvatureBound (z : ℝ) : ℝ :=
  ((4 / 3) + (8 / 15) * (z / (1 - z))) / ((1 - z) ^ 2 * (1 + z / 3) ^ 3)

theorem smallCurvatureBound_lt_ten_sevenths {z : ℝ}
    (hz0 : 0 ≤ z) (hz25 : z ≤ 1 / 25) : smallCurvatureBound z < 10 / 7 := by
  have hz1 : 0 < 1 - z := by linarith
  have hratio : z / (1 - z) ≤ 1 / 24 := (div_le_iff₀ hz1).mpr (by linarith)
  have hnum : (4 / 3 : ℝ) + (8 / 15) * (z / (1 - z)) ≤ 61 / 45 := by linarith
  have hzsq : z ^ 2 ≤ 1 / 625 := by
    nlinarith [mul_nonneg hz0 (show 0 ≤ 1 / 25 - z by linarith)]
  have hcube : 1 + z ≤ (1 + z / 3) ^ 3 := by
    nlinarith [sq_nonneg z, pow_nonneg hz0 3]
  have hbase : (599 / 625 : ℝ) ≤ (1 - z) ^ 2 * (1 + z) := by
    nlinarith [pow_nonneg hz0 3]
  have hden : (599 / 625 : ℝ) ≤ (1 - z) ^ 2 * (1 + z / 3) ^ 3 :=
    hbase.trans (mul_le_mul_of_nonneg_left hcube (sq_nonneg _))
  have hden0 : 0 < (1 - z) ^ 2 * (1 + z / 3) ^ 3 := by linarith
  apply (div_lt_iff₀ hden0).mpr
  calc
    (4 / 3 : ℝ) + (8 / 15) * (z / (1 - z)) ≤ 61 / 45 := hnum
    _ < (10 / 7) * (599 / 625) := by norm_num
    _ ≤ (10 / 7) * ((1 - z) ^ 2 * (1 + z / 3) ^ 3) :=
      mul_le_mul_of_nonneg_left hden (by norm_num)

theorem ten_sevenths_lt_inv_ell : (10 / 7 : ℝ) < 1 / ell := by
  have hpos : 0 < ell := Real.log_pos (by norm_num)
  apply (lt_div_iff₀ hpos).mpr
  have h := ell_lt_347_div_500
  linarith

theorem smallCurvatureBound_lt_inv_ell {z : ℝ}
    (hz0 : 0 ≤ z) (hz25 : z ≤ 1 / 25) : smallCurvatureBound z < 1 / ell :=
  (smallCurvatureBound_lt_ten_sevenths hz0 hz25).trans ten_sevenths_lt_inv_ell

theorem largeCurvature_first_term_le {y : ℝ} (hy : 0 ≤ y) :
    (1 - y) * (1 + (10 / 9) * y) ^ 2 ≤ 13718 / 10935 := by
  have h : 0 ≤ (y - 11 / 30) ^ 2 * ((100 / 81) * y + 460 / 243) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith

theorem largeCurvature_second_term_le {y : ℝ} (hy0 : 0 ≤ y) (hy5 : y ≤ 5 / 11) :
    (1 + y) * (1 + (10 / 9) * y) ^ 2 / 81 ≤ 355216 / 8732691 := by
  calc
    (1 + y) * (1 + (10 / 9) * y) ^ 2 / 81 ≤
        (1 + (5 / 11 : ℝ)) * (1 + (10 / 9) * (5 / 11)) ^ 2 / 81 := by
      gcongr
    _ = 355216 / 8732691 := by norm_num

theorem largeCurvature_rational_sum :
    (13718 / 10935 : ℝ) + 355216 / 8732691 < 4 / 3 := by norm_num

theorem largeCurvatureEnvelope_lt {y : ℝ} (hy0 : 0 ≤ y) (hy5 : y ≤ 5 / 11) :
    (1 / 2 : ℝ) * ((1 - y) * (1 + (10 / 9) * y) ^ 2 +
      (1 + y) * (1 + (10 / 9) * y) ^ 2 / 81) < 2 / 3 := by
  have h1 := largeCurvature_first_term_le hy0
  have h2 := largeCurvature_second_term_le hy0 hy5
  have h3 := largeCurvature_rational_sum
  linarith

end LeanBlast.CourtadeKumar

end

end OAI
