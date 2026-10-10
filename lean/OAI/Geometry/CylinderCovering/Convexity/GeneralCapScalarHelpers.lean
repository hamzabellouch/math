import Mathlib

namespace OAI

namespace CylinderCovering.GeneralCapScalarHelpers

lemma profile_bounds {q : ℝ} (hq : |q| ≤ 1) :
    0 ≤ (q ^ 2 + q ^ 4) / 16 ∧ (q ^ 2 + q ^ 4) / 16 ≤ 1 / 8 := by
  have hq2 : q ^ 2 ≤ 1 := by
    nlinarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have hq4 : q ^ 4 ≤ 1 := by
    nlinarith [sq_nonneg q, mul_self_le_mul_self (sq_nonneg q) hq2]
  constructor
  · positivity
  · linarith

lemma abs_product_le_one {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |x * y| ≤ 1 := by
  rw [abs_mul]
  nlinarith [abs_nonneg x, abs_nonneg y,
    mul_le_mul hx hy (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1)]

lemma weighted_error {ε E x y e f : ℝ}
    (hε : 0 ≤ ε) (hE : 0 ≤ E) (hxy : |x| + |y| ≤ 1)
    (he : |e| ≤ E) (hf : |f| ≤ E) :
    -ε * x * e + ε * y * f ≤ ε * E := by
  have h1 : -ε * x * e ≤ ε * |x| * E := by
    calc
      _ ≤ |-ε * x * e| := le_abs_self _
      _ = ε * |x| * |e| := by simp [abs_mul, abs_of_nonneg hε]
      _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)
  have h2 : ε * y * f ≤ ε * |y| * E := by
    calc
      _ ≤ |ε * y * f| := le_abs_self _
      _ = ε * |y| * |f| := by simp [abs_mul, abs_of_nonneg hε]
      _ ≤ _ := mul_le_mul_of_nonneg_left hf (by positivity)
  have h3 := mul_le_mul_of_nonneg_right hxy (mul_nonneg hε hE)
  nlinarith only [h1, h2, h3]

lemma radial_identity {ε x y q p a b β γ r s : ℝ}
    (hrs : r + s = 1 - ε * x * β + ε * y * γ)
    (hy : y = r * q + ε * x * a) (hx : x = s * p - ε * y * b) :
    (r - 1 / 2) * (1 - ε * x * q) + (s - 1 / 2) * (1 + ε * y * p) =
      ε ^ 2 * (x ^ 2 * a + y ^ 2 * b) - ε * x * (β - q / 2) +
        ε * y * (γ - p / 2) := by
  have hq : r * q = y - ε * x * a := by linarith
  have hp : s * p = x + ε * y * b := by linarith
  calc
    _ = r + s - 1 - ε * x * (r * q) + ε * x * q / 2 +
        ε * y * (s * p) - ε * y * p / 2 := by ring
    _ = _ := by rw [hrs, hq, hp]; ring

lemma radial_lower {ε M r f : ℝ} (hε : ε < 1)
    (hM : 0 ≤ M) (hr : 1 / 2 + ε ^ 2 * M < r) (hf : 1 - ε ≤ f) :
    ε ^ 2 * M * (1 - ε) < (r - 1 / 2) * f := by
  calc
    _ ≤ ε ^ 2 * M * f := mul_le_mul_of_nonneg_left hf (by positivity)
    _ < _ := mul_lt_mul_of_pos_right (by linarith only [hr])
      (by linarith only [hε, hf])

lemma rough_angle {ε x y q a r : ℝ} (hε : 0 ≤ ε)
    (hx : |x| ≤ 1) (hq : |q| ≤ 1) (ha : |a| ≤ 1)
    (hr0 : 1 / 2 ≤ r) (hr1 : r ≤ 1 / 2 + ε)
    (hy : y = r * q + ε * x * a) : |y - q / 2| ≤ 2 * ε := by
  have hid : y - q / 2 = (r - 1 / 2) * q + ε * x * a := by rw [hy]; ring
  have h1 : |(r - 1 / 2) * q| ≤ ε := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ r - 1 / 2)]
    calc
      _ ≤ (r - 1 / 2) * 1 := mul_le_mul_of_nonneg_left hq (by linarith)
      _ ≤ _ := by linarith
  have h2 : |ε * x * a| ≤ ε := by
    have hxa := abs_product_le_one hx ha
    calc
      _ = ε * |x * a| := by simp [abs_mul, abs_of_nonneg hε, mul_assoc]
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hxa hε
      _ = ε := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith)

lemma rough_square {ε x p : ℝ} (hε : 0 ≤ ε)
    (hx : |x| ≤ 1) (hp : |p| ≤ 1) (h : |x - p / 2| ≤ 2 * ε) :
    |x ^ 2 - p ^ 2 / 4| ≤ 3 * ε := by
  have hsum : |x + p / 2| ≤ 3 / 2 := by
    have h' := abs_add_le x (p / 2)
    rw [abs_div] at h'
    norm_num at h'
    linarith
  calc
    _ = |x - p / 2| * |x + p / 2| := by rw [← abs_mul]; congr 1; ring
    _ ≤ (2 * ε) * (3 / 2) :=
      mul_le_mul h hsum (abs_nonneg _) (by positivity)
    _ = 3 * ε := by ring

lemma cross_term_bound {ε E x y p q a b : ℝ}
    (hε : 0 ≤ ε) (hE : 0 ≤ E) (hp : |p| ≤ 1) (hq : |q| ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hxp : |x ^ 2 - p ^ 2 / 4| ≤ 3 * ε)
    (hyq : |y ^ 2 - q ^ 2 / 4| ≤ 3 * ε)
    (ha : |a - (1 + q ^ 2) / 4| ≤ E)
    (hb : |b - (1 + p ^ 2) / 4| ≤ E) :
    x ^ 2 * a + y ^ 2 * b ≤
      (p ^ 2 + p ^ 4) / 16 + (q ^ 2 + q ^ 4) / 16 + 6 * ε + E / 2 := by
  have hp2 : p ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hp).1, (abs_le.mp hp).2]
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have hxa : x ^ 2 * a ≤ p ^ 2 / 4 * ((1 + q ^ 2) / 4) + 3 * ε + E / 4 := by
    have h1 := mul_le_mul_of_nonneg_right (abs_le.mp hxp).2 ha0
    have h2 := mul_le_mul_of_nonneg_left ha1 hε
    have h3 := mul_le_mul_of_nonneg_left (abs_le.mp ha).2 (sq_nonneg p)
    have h4 := mul_le_mul_of_nonneg_right hp2 hE
    nlinarith only [h1, h2, h3, h4]
  have hyb : y ^ 2 * b ≤ q ^ 2 / 4 * ((1 + p ^ 2) / 4) + 3 * ε + E / 4 := by
    have h1 := mul_le_mul_of_nonneg_right (abs_le.mp hyq).2 hb0
    have h2 := mul_le_mul_of_nonneg_left hb1 hε
    have h3 := mul_le_mul_of_nonneg_left (abs_le.mp hb).2 (sq_nonneg q)
    have h4 := mul_le_mul_of_nonneg_right hq2 hE
    nlinarith only [h1, h2, h3, h4]
  nlinarith only [hxa, hyb, sq_nonneg (p ^ 2 - q ^ 2)]

end CylinderCovering.GeneralCapScalarHelpers

end OAI
