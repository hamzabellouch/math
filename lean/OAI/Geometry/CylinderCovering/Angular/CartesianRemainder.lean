import OAI.Geometry.CylinderCovering.Angular.CartesianFailure

namespace OAI

namespace AngularCartesianValidation

theorem sqrt_quarter_cubic_remainder {v : ℝ} (hv : |v| ≤ 1 / 8) :
    |Real.sqrt (1 / 4 + v) - (1 / 2 + v - v ^ 2)| ≤ 6 * |v| ^ 3 := by
  have hvl := (abs_le.mp hv).1
  have hvr := (abs_le.mp hv).2
  have hv2 : v ^ 2 ≤ 1 / 64 := by nlinarith only [hvl, hvr]
  have hq : 0 ≤ 1 / 4 + v := by linarith
  let r := Real.sqrt (1 / 4 + v)
  let p := 1 / 2 + v - v ^ 2
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = 1 / 4 + v := Real.sq_sqrt hq
  have hr : 1 / 4 ≤ r := by nlinarith only [hr0, hrsq, hvl]
  have hp : 1 / 4 ≤ p := by dsimp [p]; linarith
  have hden : 1 / 2 ≤ r + p := by linarith
  have hden0 : 0 ≤ r + p := by linarith
  have hid : (r - p) * (r + p) = 2 * v ^ 3 - v ^ 4 := by
    dsimp [p]
    nlinarith only [hrsq]
  have hv4 : |v| ^ 4 ≤ |v| ^ 3 := by
    have hv1 : |v| ≤ 1 := hv.trans (by norm_num)
    nlinarith only [mul_le_mul_of_nonneg_left hv1 (pow_nonneg (abs_nonneg v) 3)]
  have hres : |2 * v ^ 3 - v ^ 4| ≤ 3 * |v| ^ 3 := by
    calc
      |2 * v ^ 3 - v ^ 4| ≤ |2 * v ^ 3| + |v ^ 4| := abs_sub _ _
      _ = 2 * |v| ^ 3 + |v| ^ 4 := by rw [abs_mul, abs_pow, abs_pow]; norm_num
      _ ≤ 3 * |v| ^ 3 := by linarith
  have hprod : |r - p| * (r + p) ≤ 3 * |v| ^ 3 := by
    calc
      |r - p| * (r + p) = |(r - p) * (r + p)| := by
        rw [abs_mul, abs_of_nonneg hden0]
      _ = |2 * v ^ 3 - v ^ 4| := congrArg abs hid
      _ ≤ 3 * |v| ^ 3 := hres
  have hlo : |r - p| / 2 ≤ |r - p| * (r + p) := by
    nlinarith only [mul_nonneg (abs_nonneg (r - p)) (sub_nonneg.mpr hden)]
  change |r - p| ≤ 6 * |v| ^ 3
  linarith only [hlo, hprod]

theorem linear_quadratic_perturbation_bound {τ z a M : ℝ}
    (hτ : 0 ≤ τ) (hz : |z| ≤ 1) (ha : |a| ≤ M)
    (hsmall : τ * M ≤ 1) :
    |τ * z + τ ^ 2 * a| ≤ 2 * τ := by
  calc
    |τ * z + τ ^ 2 * a| ≤ |τ * z| + |τ ^ 2 * a| := abs_add_le _ _
    _ = τ * |z| + τ ^ 2 * |a| := by
      rw [abs_mul, abs_of_nonneg hτ, abs_mul, abs_of_nonneg (sq_nonneg τ)]
    _ ≤ τ * 1 + τ ^ 2 * M := by gcongr
    _ ≤ 2 * τ := by
      nlinarith only [mul_le_mul_of_nonneg_left hsmall hτ]

theorem linear_quadratic_square_error {τ z a M : ℝ}
    (hτ : 0 ≤ τ) (hz : |z| ≤ 1) (ha : |a| ≤ M)
    (hsmall : τ * M ≤ 1) :
    |(τ * z + τ ^ 2 * a) ^ 2 - (τ * z) ^ 2| ≤ 3 * M * τ ^ 3 := by
  have hv := linear_quadratic_perturbation_bound hτ hz ha hsmall
  have hzτ : |τ * z| ≤ τ := by
    rw [abs_mul, abs_of_nonneg hτ]
    nlinarith only [mul_le_mul_of_nonneg_left hz hτ]
  have hplus : |(τ * z + τ ^ 2 * a) + τ * z| ≤ 3 * τ :=
    (abs_add_le _ _).trans (by linarith)
  have hminus : |(τ * z + τ ^ 2 * a) - τ * z| ≤ τ ^ 2 * M := by
    calc
      |(τ * z + τ ^ 2 * a) - τ * z| = τ ^ 2 * |a| := by
        rw [add_sub_cancel_left, abs_mul, abs_of_nonneg (sq_nonneg τ)]
      _ ≤ τ ^ 2 * M := mul_le_mul_of_nonneg_left ha (sq_nonneg τ)
  have hM : 0 ≤ M := (abs_nonneg a).trans ha
  calc
    |(τ * z + τ ^ 2 * a) ^ 2 - (τ * z) ^ 2| =
        |(τ * z + τ ^ 2 * a) - τ * z| * |(τ * z + τ ^ 2 * a) + τ * z| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ (τ ^ 2 * M) * (3 * τ) :=
      mul_le_mul hminus hplus (abs_nonneg _) (mul_nonneg (sq_nonneg τ) hM)
    _ = 3 * M * τ ^ 3 := by ring

theorem paired_sqrt_cubic_remainder {τ z a b M : ℝ}
    (hτ : 0 ≤ τ) (hz : |z| ≤ 1) (ha : |a| ≤ M) (hb : |b| ≤ M)
    (hM : 1 ≤ M) (hsmall : τ * M ≤ 1 / 16) :
    |Real.sqrt (1 / 4 + τ * z + τ ^ 2 * a) +
        Real.sqrt (1 / 4 - τ * z + τ ^ 2 * b) -
        (1 + τ ^ 2 * (a + b - 2 * z ^ 2))| ≤ 128 * M * τ ^ 3 := by
  have hsmall1 : τ * M ≤ 1 := hsmall.trans (by norm_num)
  have hτ16 : τ ≤ 1 / 16 := by
    nlinarith only [mul_le_mul_of_nonneg_left hM hτ, hsmall]
  have hnz : |-z| ≤ 1 := by simpa only [abs_neg] using hz
  have hva := linear_quadratic_perturbation_bound hτ hz ha hsmall1
  have hvb := linear_quadratic_perturbation_bound hτ hnz hb hsmall1
  have hqa := sqrt_quarter_cubic_remainder (hva.trans (by linarith : 2 * τ ≤ 1 / 8))
  have hqb := sqrt_quarter_cubic_remainder (hvb.trans (by linarith : 2 * τ ≤ 1 / 8))
  have hpowA : |τ * z + τ ^ 2 * a| ^ 3 ≤ (2 * τ) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hva 3
  have hpowB : |τ * -z + τ ^ 2 * b| ^ 3 ≤ (2 * τ) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hvb 3
  have hqa' : |Real.sqrt (1 / 4 + (τ * z + τ ^ 2 * a)) -
      (1 / 2 + (τ * z + τ ^ 2 * a) - (τ * z + τ ^ 2 * a) ^ 2)| ≤ 48 * τ ^ 3 := by
    nlinarith only [hqa, hpowA]
  have hqb' : |Real.sqrt (1 / 4 + (τ * -z + τ ^ 2 * b)) -
      (1 / 2 + (τ * -z + τ ^ 2 * b) - (τ * -z + τ ^ 2 * b) ^ 2)| ≤ 48 * τ ^ 3 := by
    nlinarith only [hqb, hpowB]
  have hsa := linear_quadratic_square_error hτ hz ha hsmall1
  have hsb := linear_quadratic_square_error hτ hnz hb hsmall1
  have hMτ : τ ^ 3 ≤ M * τ ^ 3 := by
    nlinarith only [mul_le_mul_of_nonneg_right hM (pow_nonneg hτ 3)]
  rw [abs_le] at hqa' hqb' hsa hsb ⊢
  have hrewA : 1 / 4 + (τ * z + τ ^ 2 * a) = 1 / 4 + τ * z + τ ^ 2 * a := by ring
  have hrewB : 1 / 4 + (τ * -z + τ ^ 2 * b) = 1 / 4 - τ * z + τ ^ 2 * b := by ring
  rw [hrewA] at hqa'
  rw [hrewB] at hqb'
  constructor <;> nlinarith only [hqa'.1, hqa'.2, hqb'.1, hqb'.2,
    hsa.1, hsa.2, hsb.1, hsb.2, hMτ, pow_nonneg hτ 3]

theorem cartesian_root_sum_expansion {x y τ η : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (hsmall : τ * (2 + η) ≤ 1 / 16) :
    |Real.sqrt (1 / 4 + τ * x * y +
          τ ^ 2 * ((y ^ 2 / 4 + y ^ 4) + η / 2 - x ^ 2 / 4)) +
        Real.sqrt (1 / 4 - τ * x * y +
          τ ^ 2 * ((x ^ 2 / 4 + x ^ 4) + η / 2 - y ^ 2 / 4)) -
        (1 + τ ^ 2 * ((x ^ 2 - y ^ 2) ^ 2 + η))| ≤
      128 * (2 + η) * τ ^ 3 := by
  have hx2 : x ^ 2 ≤ 1 := by
    nlinarith only [(abs_le.mp hx).1, (abs_le.mp hx).2]
  have hy2 : y ^ 2 ≤ 1 := by
    nlinarith only [(abs_le.mp hy).1, (abs_le.mp hy).2]
  have hx4 : x ^ 4 ≤ 1 := by
    nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx2), hx2]
  have hy4 : y ^ 4 ≤ 1 := by
    nlinarith only [mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hy2), hy2]
  have hz : |x * y| ≤ 1 := by
    rw [abs_mul]
    nlinarith only [mul_le_mul hx hy (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1)]
  have ha : |(y ^ 2 / 4 + y ^ 4) + η / 2 - x ^ 2 / 4| ≤ 2 + η := by
    rw [abs_le]
    constructor <;> nlinarith only [hx2, hy2, hx4, hy4, hη,
      sq_nonneg x, sq_nonneg y, sq_nonneg (x ^ 2), sq_nonneg (y ^ 2)]
  have hb : |(x ^ 2 / 4 + x ^ 4) + η / 2 - y ^ 2 / 4| ≤ 2 + η := by
    rw [abs_le]
    constructor <;> nlinarith only [hx2, hy2, hx4, hy4, hη,
      sq_nonneg x, sq_nonneg y, sq_nonneg (x ^ 2), sq_nonneg (y ^ 2)]
  have h := paired_sqrt_cubic_remainder hτ hz ha hb (by linarith : 1 ≤ 2 + η) hsmall
  have hid : ((y ^ 2 / 4 + y ^ 4) + η / 2 - x ^ 2 / 4) +
      ((x ^ 2 / 4 + x ^ 4) + η / 2 - y ^ 2 / 4) - 2 * (x * y) ^ 2 =
      (x ^ 2 - y ^ 2) ^ 2 + η := by ring
  rw [hid] at h
  simpa only [mul_assoc] using h

theorem cartesian_root_sum_gt_one {x y τ η : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hτ : 0 < τ) (hη : 0 < η)
    (hsmall : τ * (2 + η) ≤ 1 / 16)
    (hmargin : τ * (256 * (2 + η)) ≤ η) :
    1 < Real.sqrt (1 / 4 + τ * x * y +
          τ ^ 2 * ((y ^ 2 / 4 + y ^ 4) + η / 2 - x ^ 2 / 4)) +
        Real.sqrt (1 / 4 - τ * x * y +
          τ ^ 2 * ((x ^ 2 / 4 + x ^ 4) + η / 2 - y ^ 2 / 4)) := by
  have hexp := cartesian_root_sum_expansion hx hy hτ.le hη.le hsmall
  have hbudget := mul_le_mul_of_nonneg_right hmargin (sq_nonneg τ)
  have hpositive := mul_pos hη (sq_pos_of_pos hτ)
  have hquartic := mul_nonneg (sq_nonneg τ) (sq_nonneg (x ^ 2 - y ^ 2))
  nlinarith only [(abs_le.mp hexp).1, hbudget, hpositive, hquartic]

end AngularCartesianValidation

end OAI
