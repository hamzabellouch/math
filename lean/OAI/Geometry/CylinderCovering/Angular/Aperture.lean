import OAI.Geometry.CylinderCovering.Angular.ApertureDefinitions

namespace OAI

open Set
noncomputable section
namespace AngularAperture

lemma transverse_nonneg (y : ℝ) : 0 ≤ transverse y := by
  unfold transverse
  positivity

lemma transverse_half (q : ℝ) : transverse (q / 2) = profile q := by
  unfold transverse profile
  ring

lemma transverse_le {y : ℝ} (hy : |y| ≤ 1) : transverse y ≤ 5 / 4 := by
  have hy2 : y ^ 2 ≤ 1 := by nlinarith [abs_le.mp hy, sq_abs y]
  have hy4 : y ^ 4 ≤ 1 := by nlinarith [sq_nonneg (y ^ 2 - 1), sq_nonneg y]
  unfold transverse
  linarith

lemma transverse_lipschitz {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |transverse x - transverse y| ≤ (9 / 2 : ℝ) * |x - y| := by
  have hx2 : |x ^ 2| ≤ 1 := by simpa only [abs_pow] using pow_le_one₀ (abs_nonneg x) hx
  have hy2 : |y ^ 2| ≤ 1 := by simpa only [abs_pow] using pow_le_one₀ (abs_nonneg y) hy
  have hxy : |x + y| ≤ 2 := (abs_add_le x y).trans (by linarith)
  have hsum : |1 / 4 + x ^ 2 + y ^ 2| ≤ 9 / 4 := by
    calc
      |1 / 4 + x ^ 2 + y ^ 2| ≤ |1 / 4 + x ^ 2| + |y ^ 2| := abs_add_le _ _
      _ ≤ |(1 / 4 : ℝ)| + |x ^ 2| + |y ^ 2| := by gcongr; exact abs_add_le _ _
      _ ≤ 9 / 4 := by
        have hquarter : |(1 / 4 : ℝ)| = 1 / 4 := by norm_num
        rw [hquarter]
        linarith
  have hid : transverse x - transverse y =
      (x - y) * (x + y) * (1 / 4 + x ^ 2 + y ^ 2) := by
    unfold transverse
    ring
  rw [hid, abs_mul, abs_mul]
  calc
    |x - y| * |x + y| * |1 / 4 + x ^ 2 + y ^ 2| ≤ |x - y| * 2 * (9 / 4) := by gcongr
    _ = (9 / 2 : ℝ) * |x - y| := by ring

lemma tau_sq_le {τ : ℝ} (hτ : |τ| ≤ 1 / 4) : τ ^ 2 ≤ 1 / 16 := by
  nlinarith [(abs_le.mp hτ).1, (abs_le.mp hτ).2, sq_abs τ]

lemma level_strictMonoOn {τ η q : ℝ} (hτ : |τ| ≤ 1 / 4) (hq : |q| ≤ 1) :
    StrictMonoOn (level τ η q) (Icc 0 1) := by
  intro x hx y hy hxy
  have hxabs : |q * x| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hx.1]
    exact (mul_le_of_le_one_left hx.1 hq).trans hx.2
  have hyabs : |q * y| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hy.1]
    exact (mul_le_of_le_one_left hy.1 hq).trans hy.2
  have hD := transverse_lipschitz hxabs hyabs
  have hdist : |q * x - q * y| ≤ y - x := by
    rw [← mul_sub, abs_mul, abs_of_neg (sub_neg.mpr hxy)]
    nlinarith [abs_nonneg q]
  have hD' : transverse (q * y) - transverse (q * x) ≤ (9 / 2 : ℝ) * (y - x) := by
    have := (abs_le.mp hD).1
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hD' (sq_nonneg τ)
  have ht := tau_sq_le hτ
  have hbound := mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr hxy.le)
  unfold level
  nlinarith

lemma root_remainder {τ η q r : ℝ} (hq : |q| ≤ 1)
    (hη1 : η ≤ 1)
    (hr : r ∈ Icc (1 / 2 : ℝ) (3 / 4)) (hroot : level τ η q r = 0) :
    |r - (1 / 2 + τ ^ 2 * (profile q + η))| ≤ (81 / 8 : ℝ) * τ ^ 4 := by
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have habs : |q * r| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hr0]
    nlinarith [hr.2]
  have hhalf : |q / 2| ≤ 1 := by
    rw [abs_div]
    norm_num
    linarith
  have hD := transverse_le habs
  have hDelta : r - 1 / 2 ≤ (9 / 4 : ℝ) * τ ^ 2 := by
    have hh : transverse (q * r) + η ≤ 9 / 4 := by linarith
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg τ)
    unfold level at hroot
    nlinarith
  have hlip := transverse_lipschitz habs hhalf
  have hdist : |q * r - q / 2| ≤ r - 1 / 2 := by
    have hid : q * r - q / 2 = q * (r - 1 / 2) := by ring
    rw [hid, abs_mul, abs_of_nonneg (sub_nonneg.mpr hr.1)]
    exact mul_le_of_le_one_left (sub_nonneg.mpr hr.1) hq
  have hb : |transverse (q * r) - transverse (q / 2)| ≤
      (9 / 2 : ℝ) * (r - 1 / 2) := hlip.trans (by gcongr)
  have heq : r - (1 / 2 + τ ^ 2 * (profile q + η)) =
      τ ^ 2 * (transverse (q * r) - transverse (q / 2)) := by
    rw [transverse_half]
    unfold level at hroot
    nlinarith
  rw [heq, abs_mul, abs_of_nonneg (sq_nonneg τ)]
  have hm1 := mul_le_mul_of_nonneg_left hb (sq_nonneg τ)
  have hm2 := mul_le_mul_of_nonneg_left hDelta (sq_nonneg τ)
  nlinarith

lemma roots_lipschitz {τ η q p r s : ℝ} (hτ : |τ| ≤ 1 / 4)
    (hq : |q| ≤ 1) (hp : |p| ≤ 1)
    (hr : r ∈ Icc (1 / 2 : ℝ) (3 / 4))
    (hs : s ∈ Icc (1 / 2 : ℝ) (3 / 4))
    (hrootr : level τ η q r = 0) (hroots : level τ η p s = 0) :
    |r - s| ≤ 7 * τ ^ 2 * |q - p| := by
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hqr : |q * r| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hr0]
    nlinarith [hr.2]
  have hps : |p * s| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hs0]
    nlinarith [hs.2]
  have hcoord : |q * r - p * s| ≤ |r - s| + |q - p| := by
    have hid : q * r - p * s = q * (r - s) + (q - p) * s := by ring
    rw [hid]
    calc
      |q * (r - s) + (q - p) * s| ≤ |q * (r - s)| + |(q - p) * s| := abs_add_le _ _
      _ = |q| * |r - s| + |q - p| * s := by rw [abs_mul, abs_mul, abs_of_nonneg hs0]
      _ ≤ |r - s| + |q - p| := by
        have h1 := mul_le_of_le_one_left (abs_nonneg (r - s)) hq
        have h2 := mul_le_of_le_one_right (abs_nonneg (q - p)) (show s ≤ 1 by linarith [hs.2])
        linarith
  have hD : |transverse (q * r) - transverse (p * s)| ≤
      (9 / 2 : ℝ) * (|r - s| + |q - p|) :=
    (transverse_lipschitz hqr hps).trans (by gcongr)
  have heq : r - s = τ ^ 2 * (transverse (q * r) - transverse (p * s)) := by
    unfold level at hrootr hroots
    nlinarith
  have hself : |r - s| ≤ τ ^ 2 * ((9 / 2 : ℝ) * (|r - s| + |q - p|)) := by
    calc
      |r - s| = τ ^ 2 * |transverse (q * r) - transverse (p * s)| := by
        rw [heq, abs_mul, abs_of_nonneg (sq_nonneg τ)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hD (sq_nonneg τ)
  have habs := mul_le_mul_of_nonneg_right (tau_sq_le hτ) (abs_nonneg (r - s))
  have hn := mul_nonneg (sq_nonneg τ) (abs_nonneg (q - p))
  nlinarith

end AngularAperture

end

end OAI
