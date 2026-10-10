import OAI.Geometry.CylinderCovering.Cartesian.CapsDefinitions

namespace OAI

namespace CylinderCovering.CartesianCaps

theorem sqrt_quarter_cubic_remainder {v : ℝ} (hv : -(1 / 4 : ℝ) ≤ v) :
    |Real.sqrt (1 / 4 + v) - (1 / 2 + v - v ^ 2)| ≤ 12 * |v| ^ 3 := by
  let z : ℝ := Real.sqrt (1 / 4 + v) - 1 / 2
  have ht0 := Real.sqrt_nonneg (1 / 4 + v)
  have ht2 := Real.sq_sqrt (show 0 ≤ 1 / 4 + v by linarith)
  have hzid : v = z + z ^ 2 := by dsimp [z]; nlinarith only [ht2]
  have hzlower : -(1 / 2 : ℝ) ≤ z := by dsimp [z]; linarith only [ht0]
  have hzbound : |z| ≤ 2 * |v| := by
    by_cases hz : 0 ≤ z
    · rw [abs_of_nonneg hz]
      have hv0 : 0 ≤ v := by nlinarith only [hzid, hz, sq_nonneg z]
      rw [abs_of_nonneg hv0]
      nlinarith only [hzid, hz, sq_nonneg z]
    · have hz0 := le_of_not_ge hz
      rw [abs_of_nonpos hz0]
      have hv0 : v ≤ 0 := by nlinarith only [hzid, hz0, hzlower]
      rw [abs_of_nonpos hv0]
      nlinarith only [hzid, hz0, hzlower]
  have hvz : |v + z| ≤ 3 * |v| := (abs_add_le _ _).trans (by linarith)
  have hzsq : |z| ^ 2 ≤ (2 * |v|) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hzbound
  calc
    _ = |z ^ 2 * (v + z)| := by
      congr 1
      dsimp [z] at *
      nlinarith only [ht2]
    _ = |z| ^ 2 * |v + z| := by rw [abs_mul, abs_pow]
    _ ≤ (2 * |v|) ^ 2 * (3 * |v|) :=
      mul_le_mul hzsq hvz (abs_nonneg _) (by positivity)
    _ = 12 * |v| ^ 3 := by ring

theorem sqrt_quarter_perturbed_remainder {τ M a B : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hM : 0 ≤ M)
    (ha : |a| ≤ 1) (hB : |B| ≤ M) (hsmall : (M + 1) * τ ≤ 1 / 4) :
    |Real.sqrt (1 / 4 + τ * a + τ ^ 2 * B) -
      (1 / 2 + τ * a + τ ^ 2 * (B - a ^ 2))| ≤
      (12 * (M + 1) ^ 3 + M * (M + 2)) * τ ^ 3 := by
  let v : ℝ := τ * a + τ ^ 2 * B
  have hτ2 : τ ^ 2 ≤ τ := by nlinarith
  have haτ : |τ * a| ≤ τ := by
    rw [abs_mul, abs_of_nonneg hτ0]
    simpa using mul_le_mul_of_nonneg_left ha hτ0
  have hBτ : |τ ^ 2 * B| ≤ τ ^ 2 * M := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg τ)]
    exact mul_le_mul_of_nonneg_left hB (sq_nonneg τ)
  have hv : |v| ≤ (M + 1) * τ := by
    have hMτ := mul_le_mul_of_nonneg_left hτ2 hM
    exact (abs_add_le _ _).trans (by nlinarith only [haτ, hBτ, hMτ])
  have hvdom : -(1 / 4 : ℝ) ≤ v := by
    linarith only [(abs_le.mp hv).1, hsmall]
  have hvpow : |v| ^ 3 ≤ ((M + 1) * τ) ^ 3 := by gcongr
  have htaylor : |Real.sqrt (1 / 4 + v) - (1 / 2 + v - v ^ 2)| ≤
      12 * (M + 1) ^ 3 * τ ^ 3 := by
    calc
      _ ≤ 12 * |v| ^ 3 := sqrt_quarter_cubic_remainder hvdom
      _ ≤ 12 * ((M + 1) * τ) ^ 3 := by gcongr
      _ = 12 * (M + 1) ^ 3 * τ ^ 3 := by ring
  have hplus : |v + τ * a| ≤ (M + 2) * τ :=
    (abs_add_le _ _).trans (by nlinarith only [hv, haτ])
  have hminus : |v - τ * a| ≤ τ ^ 2 * M := by
    simpa [v] using hBτ
  have hsq : |v ^ 2 - (τ * a) ^ 2| ≤ M * (M + 2) * τ ^ 3 := by
    calc
      _ = |v - τ * a| * |v + τ * a| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ (τ ^ 2 * M) * ((M + 2) * τ) :=
        mul_le_mul hminus hplus (abs_nonneg _) (by positivity)
      _ = M * (M + 2) * τ ^ 3 := by ring
  have hsplit : Real.sqrt (1 / 4 + τ * a + τ ^ 2 * B) -
      (1 / 2 + τ * a + τ ^ 2 * (B - a ^ 2)) =
      (Real.sqrt (1 / 4 + v) - (1 / 2 + v - v ^ 2)) -
        (v ^ 2 - (τ * a) ^ 2) := by
    dsimp [v]
    rw [show 1 / 4 + (τ * a + τ ^ 2 * B) = 1 / 4 + τ * a + τ ^ 2 * B by ring]
    ring
  rw [hsplit]
  exact (abs_sub _ _).trans (by nlinarith only [htaylor, hsq])

theorem sqrt_quarter_pair_remainder {τ M a B C : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hM : 0 ≤ M)
    (ha : |a| ≤ 1) (hB : |B| ≤ M) (hC : |C| ≤ M)
    (hsmall : (M + 1) * τ ≤ 1 / 4) :
    |Real.sqrt (1 / 4 + τ * a + τ ^ 2 * B) +
      Real.sqrt (1 / 4 - τ * a + τ ^ 2 * C) -
      (1 + τ ^ 2 * (B + C - 2 * a ^ 2))| ≤
      (24 * (M + 1) ^ 3 + 2 * M * (M + 2)) * τ ^ 3 := by
  have hfirst := sqrt_quarter_perturbed_remainder hτ0 hτ1 hM ha hB hsmall
  have hsecond := sqrt_quarter_perturbed_remainder hτ0 hτ1 hM
    (a := -a) (by simpa only [abs_neg] using ha) hC hsmall
  have hneg : 1 / 4 + τ * -a + τ ^ 2 * C = 1 / 4 - τ * a + τ ^ 2 * C := by ring
  rw [hneg] at hsecond
  have hsplit : Real.sqrt (1 / 4 + τ * a + τ ^ 2 * B) +
      Real.sqrt (1 / 4 - τ * a + τ ^ 2 * C) -
      (1 + τ ^ 2 * (B + C - 2 * a ^ 2)) =
      (Real.sqrt (1 / 4 + τ * a + τ ^ 2 * B) -
        (1 / 2 + τ * a + τ ^ 2 * (B - a ^ 2))) +
      (Real.sqrt (1 / 4 - τ * a + τ ^ 2 * C) -
        (1 / 2 + τ * -a + τ ^ 2 * (C - (-a) ^ 2))) := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (by nlinarith only [hfirst, hsecond])

theorem cartesian_second_coefficient_bound {η x y : ℝ} (hη : 0 ≤ η)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |D y + η / 2 - x ^ 2 / 4| ≤ η + 2 := by
  have hx2 : x ^ 2 ≤ 1 := by
    nlinarith only [(abs_le.mp hx).1, (abs_le.mp hx).2]
  have hy2 : y ^ 2 ≤ 1 := by
    nlinarith only [(abs_le.mp hy).1, (abs_le.mp hy).2]
  have hy4 : y ^ 4 ≤ 1 := by
    nlinarith only [mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hy2), hy2]
  unfold D
  rw [abs_le]
  constructor <;> nlinarith only [hx2, hy2, hy4, sq_nonneg x, sq_nonneg y, sq_nonneg (y ^ 2), hη]

theorem cartesian_pair_expansion {τ η x y : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hη : 0 ≤ η)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hsmall : (η + 3) * τ ≤ 1 / 4) :
    |Real.sqrt (1 / 4 + τ * (x * y) + τ ^ 2 * (D y + η / 2 - x ^ 2 / 4)) +
      Real.sqrt (1 / 4 - τ * (x * y) + τ ^ 2 * (D x + η / 2 - y ^ 2 / 4)) -
      (1 + τ ^ 2 * ((x ^ 2 - y ^ 2) ^ 2 + η))| ≤
      (24 * (η + 3) ^ 3 + 2 * (η + 2) * (η + 4)) * τ ^ 3 := by
  have hxy : |x * y| ≤ 1 := by
    rw [abs_mul]
    calc
      |x| * |y| ≤ 1 * 1 := mul_le_mul hx hy (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have h := sqrt_quarter_pair_remainder hτ0 hτ1 (M := η + 2) (by positivity)
    hxy (cartesian_second_coefficient_bound hη hx hy)
    (cartesian_second_coefficient_bound hη hy hx) (by linarith)
  have hcoef : (D y + η / 2 - x ^ 2 / 4) + (D x + η / 2 - y ^ 2 / 4) -
      2 * (x * y) ^ 2 = (x ^ 2 - y ^ 2) ^ 2 + η := by unfold D; ring
  rw [hcoef] at h
  convert h using 1
  ring

theorem cartesian_pair_gt_one {τ η x y : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hη : 0 < η)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hsmall : (η + 3) * τ ≤ 1 / 4)
    (hmargin : (24 * (η + 3) ^ 3 + 2 * (η + 2) * (η + 4)) * τ ≤ η / 2) :
    1 < Real.sqrt (1 / 4 + τ * (x * y) + τ ^ 2 * (D y + η / 2 - x ^ 2 / 4)) +
      Real.sqrt (1 / 4 - τ * (x * y) + τ ^ 2 * (D x + η / 2 - y ^ 2 / 4)) := by
  have h := (abs_le.mp (cartesian_pair_expansion hτ.le hτ1 hη.le hx hy hsmall)).1
  have hm := mul_le_mul_of_nonneg_right hmargin (sq_nonneg τ)
  have hp := mul_pos (sq_pos_of_pos hτ) hη
  have hq := mul_nonneg (sq_nonneg τ) (sq_nonneg (x ^ 2 - y ^ 2))
  nlinarith only [h, hm, hp, hq]

theorem cartesian_edge_one_obstruction_identity (ε x y : ℝ) :
    (ε / 2) ^ 2 * (((2 * x) ^ 2 - (2 * y) ^ 2) ^ 2 + 1 / 1000) =
      ε ^ 2 * (4 * (x ^ 2 - y ^ 2) ^ 2 + 1 / 4000) := by ring

end CylinderCovering.CartesianCaps

end OAI
