import OAI.Geometry.CylinderCovering.Nilpotent.BasicDefinitions

namespace OAI

open Set

namespace CylinderCovering.Nilpotent

theorem quadratic_inversion_nonneg {z d y : ℝ}
    (hz : 0 ≤ z) (hd : 0 ≤ d) (hy : |y| ≤ z) :
    ∃ r : ℝ, |r| ≤ 1 ∧ y = r * z + d * (1 - r ^ 2) ∧ 0 ≤ z - 2 * d * r := by
  have hy' := abs_le.mp hy
  let f : ℝ → ℝ := fun r => r * z + d * (1 - r ^ 2)
  have hf : Continuous f := by fun_prop
  by_cases hdz : 2 * d ≤ z
  · have hends : y ∈ Icc (f (-1)) (f 1) := by
      dsimp [f]
      constructor <;> nlinarith
    obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1)
      hf.continuousOn hends
    refine ⟨r, abs_le.mpr hr, hfr.symm, ?_⟩
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hr.2)]
  · have hdpos : 0 < d := by linarith
    let b : ℝ := z / (2 * d)
    have hb0 : 0 ≤ b := div_nonneg hz (by positivity)
    have hb1 : b ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have hbmul : 2 * d * b = z := by
      dsimp [b]
      field_simp
    have hfb : z ≤ f b := by
      dsimp [f]
      nlinarith [sq_nonneg (1 - b)]
    have hends : y ∈ Icc (f (-1)) (f b) := by
      constructor
      · dsimp [f]; nlinarith
      · exact le_trans hy'.2 hfb
    obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc (by linarith : (-1 : ℝ) ≤ b)
      hf.continuousOn hends
    refine ⟨r, abs_le.mpr ⟨hr.1, hr.2.trans hb1⟩, hfr.symm, ?_⟩
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hr.2)]

theorem quadratic_inversion {z d y : ℝ} (hz : 0 ≤ z) (hy : |y| ≤ z) :
    ∃ r : ℝ, |r| ≤ 1 ∧ y = r * z + d * (1 - r ^ 2) ∧ 0 ≤ z - 2 * d * r := by
  by_cases hd : 0 ≤ d
  · exact quadratic_inversion_nonneg hz hd hy
  · obtain ⟨r, hr, hEq, hnonneg⟩ := quadratic_inversion_nonneg
      (d := -d) (y := -y) hz (by linarith) (by simpa using hy)
    refine ⟨-r, by simpa using hr, ?_, ?_⟩
    · nlinarith
    · nlinarith

theorem v_bounds {p : ℝ} (hp : |p| ≤ 1) : 0 ≤ v p ∧ v p ≤ 1 / 2 := by
  have hs := (sq_le_one_iff_abs_le_one p).2 hp
  dsimp [v]
  constructor <;> nlinarith [sq_nonneg p]

theorem a_bounds {p : ℝ} (hp : |p| ≤ 1) : 0 ≤ a p ∧ a p ≤ 1 / 8 := by
  have hv := v_bounds hp
  have hs := (sq_le_one_iff_abs_le_one p).2 hp
  dsimp [a]
  constructor
  · exact div_nonneg (mul_nonneg (sq_nonneg p) hv.1) (by norm_num)
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs) hv.1]

theorem height_gt_half {k : ℝ} (hk : 0 < k) (p : ℝ) : 1 / 2 < height k p := by
  have hv : 0 ≤ v p := by dsimp [v]; positivity
  have ha : 0 ≤ a p := by dsimp [a]; positivity
  have hk3 : 0 < k ^ 3 := pow_pos hk _
  dsimp [height]
  nlinarith [mul_nonneg (sq_nonneg k) ha]

theorem overlap_pair_inequality (r q : ℝ) :
    (q ^ 2 * v r + r ^ 2 * v q) / 4 ≤ a r + a q := by
  dsimp [a, v]
  nlinarith [sq_nonneg (r ^ 2 - q ^ 2)]

theorem overlap_identity {k x y r q t u : ℝ}
    (hy : y = r * t + k * x * v r)
    (hx : x = q * u - k * y * v q)
    (hsum : t + u = 1 + k / 2 * (y * q - x * r)) :
    (1 - k * r * q / 2) * (t - 1 / 2) +
        (1 + k * r * q / 2) * (u - 1 / 2) =
      k ^ 2 / 2 * (x * q * v r + y * r * v q) := by
  linear_combination hsum + (k * q / 2) * hy - (k * r / 2) * hx

theorem center_error {k p s e V : ℝ} (hk : 0 ≤ k)
    (hp : |p| ≤ 1) (hs : |s| ≤ 1) (he : 0 ≤ e) (hek : e ≤ k)
    (hV : 0 ≤ V) (hVhalf : V ≤ 1 / 2) :
    |p * e + k * s * V| ≤ 3 * k / 2 := by
  calc
    |p * e + k * s * V| ≤ |p * e| + |k * s * V| := abs_add_le _ _
    _ = |p| * e + k * |s| * V := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg he, abs_of_nonneg hk,
        abs_of_nonneg hV]
    _ ≤ 1 * k + k * 1 * (1 / 2) := by
      gcongr
    _ = 3 * k / 2 := by ring

private theorem abs_product_le_one {p q : ℝ} (hp : |p| ≤ 1) (hq : |q| ≤ 1) :
    |p * q| ≤ 1 := by
  rw [abs_mul]
  nlinarith [abs_nonneg p, abs_nonneg q]

private theorem coefficient_pos {k r q : ℝ} (hk : 0 < k) (hk1 : k < 1)
    (hr : |r| ≤ 1) (hq : |q| ≤ 1) :
    0 < 1 - k * r * q / 2 ∧ 0 < 1 + k * r * q / 2 := by
  have hp := abs_product_le_one hr hq
  have hb : |k * (r * q)| ≤ k := by
    rw [abs_mul, abs_of_pos hk]
    nlinarith
  have hb' := abs_le.mp hb
  constructor <;> nlinarith

private theorem cutoff_mix_lower {r q : ℝ} (hr : |r| ≤ 1) (hq : |q| ≤ 1) :
    -(1 / 16 : ℝ) ≤ r * q / 2 * (a q - a r) := by
  have har := a_bounds hr
  have haq := a_bounds hq
  have hdiff : |a q - a r| ≤ 1 / 8 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hp := abs_product_le_one hr hq
  have hb : |r * q / 2 * (a q - a r)| ≤ 1 / 16 := by
    calc
      |r * q / 2 * (a q - a r)| = |r * q| / 2 * |a q - a r| := by
        rw [abs_mul, abs_div]; norm_num
      _ ≤ 1 / 2 * (1 / 8) := by gcongr
      _ = 1 / 16 := by norm_num
  exact (abs_le.mp hb).1

theorem failed_cutoffs_lower {k r q t u : ℝ} (hk : 0 < k) (hk1 : k < 1)
    (hr : |r| ≤ 1) (hq : |q| ≤ 1)
    (ht : height k r < t) (hu : height k q < u) :
    k ^ 2 * (a r + a q) + (31 / 16 : ℝ) * k ^ 3 <
      (1 - k * r * q / 2) * (t - 1 / 2) +
        (1 + k * r * q / 2) * (u - 1 / 2) := by
  have hp := coefficient_pos hk hk1 hr hq
  have htl : k ^ 2 * a r + k ^ 3 < t - 1 / 2 := by
    dsimp [height] at ht; linarith
  have hul : k ^ 2 * a q + k ^ 3 < u - 1 / 2 := by
    dsimp [height] at hu; linarith
  have hstrict := add_lt_add (mul_lt_mul_of_pos_left htl hp.1)
    (mul_lt_mul_of_pos_left hul hp.2)
  have hmix := cutoff_mix_lower hr hq
  have hk3 : 0 ≤ k ^ 3 := le_of_lt (pow_pos hk _)
  have hprod := mul_nonneg hk3 (show 0 ≤ r * q / 2 * (a q - a r) + 1 / 16 by linarith)
  nlinarith

private theorem centered_product_upper {k x q V : ℝ} (hk : 0 ≤ k)
    (hq : |q| ≤ 1) (hx : |x - q / 2| ≤ 3 * k / 2)
    (hV : 0 ≤ V) (hVhalf : V ≤ 1 / 2) :
    x * q * V ≤ q ^ 2 * V / 2 + 3 * k / 4 := by
  have he : |(x - q / 2) * q * V| ≤ 3 * k / 4 := by
    calc
      |(x - q / 2) * q * V| = |x - q / 2| * |q| * V := by
        rw [abs_mul, abs_mul, abs_of_nonneg hV]
      _ ≤ (3 * k / 2) * 1 * (1 / 2) := by gcongr
      _ = 3 * k / 4 := by ring
  have he' := (abs_le.mp he).2
  nlinarith

theorem centered_overlap_upper {k x y r q : ℝ} (hk : 0 ≤ k)
    (hr : |r| ≤ 1) (hq : |q| ≤ 1)
    (hx : |x - q / 2| ≤ 3 * k / 2) (hy : |y - r / 2| ≤ 3 * k / 2) :
    k ^ 2 / 2 * (x * q * v r + y * r * v q) ≤
      k ^ 2 * (a r + a q) + (3 / 4 : ℝ) * k ^ 3 := by
  have hvr := v_bounds hr
  have hvq := v_bounds hq
  have h1 := centered_product_upper hk hq hx hvr.1 hvr.2
  have h2 := centered_product_upper hk hr hy hvq.1 hvq.2
  have hpair := overlap_pair_inequality r q
  have hsum : x * q * v r + y * r * v q ≤ 2 * (a r + a q) + 3 * k / 2 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum (show 0 ≤ k ^ 2 / 2 by positivity)
  nlinarith

theorem cutoff_alternative {k x y r q t u : ℝ} (hk : 0 < k) (hk1 : k < 1)
    (hx1 : |x| ≤ 1) (hy1 : |y| ≤ 1) (hr : |r| ≤ 1) (hq : |q| ≤ 1)
    (hy : y = r * t + k * x * v r)
    (hx : x = q * u - k * y * v q)
    (hsum : t + u = 1 + k / 2 * (y * q - x * r)) :
    t ≤ height k r ∨ u ≤ height k q := by
  by_contra h
  push Not at h
  have htHalf : 1 / 2 < t := (height_gt_half hk r).trans h.1
  have huHalf : 1 / 2 < u := (height_gt_half hk q).trans h.2
  have hyq := abs_le.mp (abs_product_le_one hy1 hq)
  have hxr := abs_le.mp (abs_product_le_one hx1 hr)
  have hsumUpper : t + u ≤ 1 + k := by
    have hp := mul_nonneg hk.le (show 0 ≤ 2 - (y * q - x * r) by linarith)
    nlinarith
  have ht0 : 0 ≤ t - 1 / 2 := by linarith
  have hu0 : 0 ≤ u - 1 / 2 := by linarith
  have htk : t - 1 / 2 ≤ k := by linarith
  have huk : u - 1 / 2 ≤ k := by linarith
  have hvr := v_bounds hr
  have hvq := v_bounds hq
  have hxcenter : |x - q / 2| ≤ 3 * k / 2 := by
    have hce := center_error hk.le hq (show |-y| ≤ 1 by simpa using hy1)
      hu0 huk hvq.1 hvq.2
    have heq : x - q / 2 = q * (u - 1 / 2) + k * (-y) * v q := by
      rw [hx]; ring
    rwa [← heq] at hce
  have hycenter : |y - r / 2| ≤ 3 * k / 2 := by
    have hce := center_error hk.le hr hx1 ht0 htk hvr.1 hvr.2
    have heq : y - r / 2 = r * (t - 1 / 2) + k * x * v r := by
      rw [hy]; ring
    rwa [← heq] at hce
  have hlower := failed_cutoffs_lower hk hk1 hr hq h.1 h.2
  have hupper := centered_overlap_upper hk.le hr hq hxcenter hycenter
  have hid := overlap_identity hy hx hsum
  have hk3 : 0 < k ^ 3 := pow_pos hk _
  linarith

theorem sweep_cover {k x y z : ℝ} (hk : 0 < k) (hk1 : k < 1)
    (hK : InTetrahedron x y z) :
    InLowerSweep k x y z ∨ InUpperSweep k x y z := by
  obtain ⟨hz0, hz1, hx, hy⟩ := hK
  have hx1 : |x| ≤ 1 := by linarith
  have hy1 : |y| ≤ 1 := by linarith
  obtain ⟨r, hr, hrEq, hrNonneg⟩ := quadratic_inversion
    (d := k * x / 4) hz0 hy
  obtain ⟨q, hq, hqEq, hqNonneg⟩ := quadratic_inversion
    (d := -(k * y / 4)) (by linarith : 0 ≤ 1 - z) hx
  let t := z - k * x * r / 2
  let u := 1 - z + k * y * q / 2
  have ht0 : 0 ≤ t := by dsimp [t]; nlinarith
  have hu0 : 0 ≤ u := by dsimp [u]; nlinarith
  have hyEq : y = r * t + k * x * v r := by
    dsimp [t, v]
    nlinarith [hrEq]
  have hxEq : x = q * u - k * y * v q := by
    dsimp [u, v]
    nlinarith [hqEq]
  have hsum : t + u = 1 + k / 2 * (y * q - x * r) := by
    dsimp [t, u]; ring
  rcases cutoff_alternative hk hk1 hx1 hy1 hr hq hyEq hxEq hsum with ht | hu
  · left
    refine ⟨r, t, hx1, hr, ht0, ht, hyEq, ?_⟩
    dsimp [t, w]; ring
  · right
    refine ⟨q, u, hy1, hq, hu0, hu, hxEq, ?_⟩
    dsimp [u, w]; ring

end CylinderCovering.Nilpotent

end OAI
