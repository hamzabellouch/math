import Mathlib

namespace OAI

namespace AngularCubic

lemma endpoint_left (a b : ℝ) :
    (1 + a * b) / 2 - a * ((a + b) / 2) = (1 - a ^ 2) / 2 := by ring

lemma endpoint_right (a b : ℝ) :
    (1 + a * b) / 2 - b * ((a + b) / 2) = (1 - b ^ 2) / 2 := by ring

lemma square_le_one {x : ℝ} (hx : |x| ≤ 1) : x ^ 2 ≤ 1 := by
  have h := abs_le.mp hx
  nlinarith [sq_nonneg (1 - x), sq_nonneg (1 + x)]

lemma product_error {x y d : ℝ} (hx : |x| ≤ d) (hy : |y| ≤ 2) :
    |x * y| ≤ 2 * d := by
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ ≤ d * 2 := mul_le_mul hx hy (abs_nonneg y) (le_trans (abs_nonneg x) hx)
    _ = 2 * d := by ring

lemma mixed_quartic_bound {a b q r d Dq Dr : ℝ}
    (ha : |a - (1 + r ^ 2) / 2| ≤ d)
    (hb : |b - (1 + q ^ 2) / 2| ≤ d)
    (hq : |q| ≤ 1) (hr : |r| ≤ 1)
    (hDq : (q ^ 2 + q ^ 4) / 2 ≤ Dq)
    (hDr : (r ^ 2 + r ^ 4) / 2 ≤ Dr) :
    a * q ^ 2 + b * r ^ 2 ≤ Dq + Dr + 2 * d := by
  have hd : 0 ≤ d := le_trans (abs_nonneg _) ha
  have hqa := mul_le_mul_of_nonneg_right (abs_le.mp ha).2 (sq_nonneg q)
  have hrb := mul_le_mul_of_nonneg_right (abs_le.mp hb).2 (sq_nonneg r)
  have hqd := mul_le_mul_of_nonneg_left (square_le_one hq) hd
  have hrd := mul_le_mul_of_nonneg_left (square_le_one hr) hd
  nlinarith [sq_nonneg (q ^ 2 - r ^ 2)]

lemma coarse_excess_bound {e d P T : ℝ}
    (he : 0 ≤ e) (hehalf : e ≤ 1 / 2) (hd : d ≤ e ^ 2)
    (hT : T ≤ 4) (hP : P ≤ e * P + e ^ 2 * T + 4 * e * d) :
    P ≤ 12 * e ^ 2 := by
  have hTd := mul_le_mul_of_nonneg_left hT (sq_nonneg e)
  have hed := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 4 * e)
  have hecube : e ^ 3 ≤ e ^ 2 / 2 := by nlinarith [sq_nonneg e]
  by_cases hp : P ≤ 0
  · linarith [sq_nonneg e]
  · have hp0 : 0 ≤ P := le_of_lt (lt_of_not_ge hp)
    have hep := mul_le_mul_of_nonneg_right hehalf hp0
    nlinarith

lemma sharpen_excess_bound {e d P T Q : ℝ}
    (he : 0 ≤ e) (hehalf : e ≤ 1 / 2) (hd : d ≤ e ^ 2)
    (_hP0 : 0 ≤ P) (hP12 : P ≤ 12 * e ^ 2)
    (hT : T ≤ Q + 2 * P + 4 * e)
    (hP : P ≤ e * P + e ^ 2 * T + 4 * e * d) :
    P ≤ e ^ 2 * Q + 32 * e ^ 3 := by
  have h1 := mul_le_mul_of_nonneg_left hT (sq_nonneg e)
  have h2 := mul_le_mul_of_nonneg_left hP12 he
  have h3 := mul_le_mul_of_nonneg_left hP12 (by positivity : 0 ≤ 2 * e ^ 2)
  have h4 := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 4 * e)
  have h5 : 24 * e ^ 4 ≤ 12 * e ^ 3 := by
    have := mul_nonneg (by linarith : 0 ≤ 1 / 2 - e) (pow_nonneg he 3)
    nlinarith
  nlinarith

lemma final_excess_bound {e d P Q Dq Dr : ℝ}
    (he : 0 ≤ e) (hehalf : e ≤ 1 / 2) (hd : d ≤ e ^ 2)
    (hP : P ≤ e ^ 2 * Q + 32 * e ^ 3)
    (hQ : Q ≤ Dq + Dr + 2 * d) :
    P ≤ e ^ 2 * (Dq + Dr) + 33 * e ^ 3 := by
  have h1 := mul_le_mul_of_nonneg_left hQ (sq_nonneg e)
  have h2 := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2 * e ^ 2)
  have h3 : 2 * e ^ 4 ≤ e ^ 3 := by
    have := mul_nonneg (by linarith : 0 ≤ 1 / 2 - e) (pow_nonneg he 3)
    nlinarith
  nlinarith

lemma abs_mul_le_one {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |x * y| ≤ 1 := by
  rw [abs_mul]
  nlinarith [abs_nonneg x, abs_nonneg y]

lemma three_factor_bound {q a x : ℝ} (hq : |q| ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : |x| ≤ 2) :
    |q * a * x| ≤ 2 := by
  have hqa : |q * a| ≤ 1 := abs_mul_le_one hq (by rwa [abs_of_nonneg ha0])
  simpa using product_error hqa hx

lemma refined_term_bound {e P a b q x y t : ℝ}
    (he : 0 ≤ e) (hP : 0 ≤ P)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hq : |q| ≤ 1) (hy : |y| ≤ 2) (ht : t ≤ 1 + P)
    (hx : x = q * t - e * b * y) :
    q * a * x ≤ a * q ^ 2 + P + 2 * e := by
  have haq0 : 0 ≤ a * q ^ 2 := mul_nonneg ha0 (sq_nonneg q)
  have haq1 : a * q ^ 2 ≤ 1 := by
    have := mul_le_mul_of_nonneg_right ha1 (sq_nonneg q)
    nlinarith [square_le_one hq]
  have hmain := mul_le_mul_of_nonneg_left ht haq0
  have hcost := mul_le_mul_of_nonneg_right haq1 hP
  have habs : |q * a * b * y| ≤ 2 := by
    have hqab : |q * a * b| ≤ 1 :=
      abs_mul_le_one (abs_mul_le_one hq (by rwa [abs_of_nonneg ha0]))
        (by rwa [abs_of_nonneg hb0])
    simpa using product_error hqab hy
  have herror := mul_le_mul_of_nonneg_left (abs_le.mp habs).1 he
  calc
    q * a * x = a * q ^ 2 * t - e * (q * a * b * y) := by rw [hx]; ring
    _ ≤ a * q ^ 2 + P + 2 * e := by nlinarith

lemma excess_identity {e s t s0 t0 x y q r a b bj bl : ℝ}
    (hst : s + t = 2) (hs : s0 = s - e * bj * x)
    (ht : t0 = t + e * bl * y)
    (hy : y = r * s0 + e * a * x)
    (hx : x = q * t0 - e * b * y) :
    s0 + t0 - 2 = e * ((bl - q) * y - (bj - r) * x +
      r * q * (s0 - t0)) + e ^ 2 * (q * a * x + r * b * y) := by
  have hbase : s0 + t0 - 2 = e * (bl * y - bj * x) := by linarith
  have hswap : q * y - r * x = r * q * (s0 - t0) +
      e * (q * a * x + r * b * y) := by
    linear_combination q * hy - r * hx
  linear_combination hbase + e * hswap

lemma excess_inequality {e d P s0 t0 x y q r a b bj bl : ℝ}
    (he : 0 ≤ e) (hP : |s0 - t0| ≤ P)
    (hx : |x| ≤ 2) (hy : |y| ≤ 2)
    (hq : |q| ≤ 1) (hr : |r| ≤ 1)
    (hbj : |bj - r| ≤ d) (hbl : |bl - q| ≤ d)
    (hid : P = e * ((bl - q) * y - (bj - r) * x +
      r * q * (s0 - t0)) + e ^ 2 * (q * a * x + r * b * y)) :
    P ≤ e * P + e ^ 2 * (q * a * x + r * b * y) + 4 * e * d := by
  have h1 := (abs_le.mp (product_error hbl hy)).2
  have h2 := (abs_le.mp (product_error hbj hx)).1
  have h3 : r * q * (s0 - t0) ≤ P := by
    have hprod : |r * q| ≤ 1 := abs_mul_le_one hr hq
    have hbound : |r * q * (s0 - t0)| ≤ P := by
      rw [abs_mul]
      have := mul_le_mul hprod hP (abs_nonneg (s0 - t0))
        (by norm_num : (0 : ℝ) ≤ 1)
      simpa using this
    exact (abs_le.mp hbound).2
  have hsum : (bl - q) * y - (bj - r) * x + r * q * (s0 - t0) ≤ P + 4 * d := by
    linarith
  have := mul_le_mul_of_nonneg_left hsum he
  nlinarith [hid]

theorem radial_restrictions {e d s t s0 t0 x y q r a b bj bl Dj Dl : ℝ}
    (he : 0 < e) (hehalf : e ≤ 1 / 2) (hd : d ≤ e ^ 2)
    (hst : s + t = 2)
    (hs : s0 = s - e * bj * x) (ht : t0 = t + e * bl * y)
    (hyEq : y = r * s0 + e * a * x)
    (hxEq : x = q * t0 - e * b * y)
    (hx : |x| ≤ 2) (hy : |y| ≤ 2)
    (hq : |q| ≤ 1) (hr : |r| ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hbj : |bj - r| ≤ d) (hbl : |bl - q| ≤ d)
    (ha : |a - (1 + r ^ 2) / 2| ≤ d)
    (hb : |b - (1 + q ^ 2) / 2| ≤ d)
    (hDj : (r ^ 2 + r ^ 4) / 2 ≤ Dj)
    (hDl : (q ^ 2 + q ^ 4) / 2 ≤ Dl) :
    s0 ≤ 1 + e ^ 2 * Dj + 100 * e ^ 3 ∨
      t0 ≤ 1 + e ^ 2 * Dl + 100 * e ^ 3 := by
  by_contra h
  push Not at h
  obtain ⟨hsFail, htFail⟩ := h
  have he0 : 0 ≤ e := le_of_lt he
  have he3 : 0 < e ^ 3 := pow_pos he 3
  have hDj0 : 0 ≤ Dj := by nlinarith only [hDj, sq_nonneg r, sq_nonneg (r ^ 2)]
  have hDl0 : 0 ≤ Dl := by nlinarith only [hDl, sq_nonneg q, sq_nonneg (q ^ 2)]
  have hs1 : 1 ≤ s0 := by nlinarith only [hsFail, he3, mul_nonneg (sq_nonneg e) hDj0]
  have ht1 : 1 ≤ t0 := by nlinarith only [htFail, he3, mul_nonneg (sq_nonneg e) hDl0]
  let P := s0 + t0 - 2
  have hP0 : 0 ≤ P := by dsimp [P]; linarith only [hs1, ht1]
  have hsP : s0 ≤ 1 + P := by dsimp [P]; linarith only [hs1, ht1]
  have htP : t0 ≤ 1 + P := by dsimp [P]; linarith only [hs1, ht1]
  have hdiff : |s0 - t0| ≤ P := by
    rw [abs_le]
    dsimp [P]
    constructor <;> linarith only [hs1, ht1]
  have hid : P = e * ((bl - q) * y - (bj - r) * x +
      r * q * (s0 - t0)) + e ^ 2 * (q * a * x + r * b * y) :=
    excess_identity hst hs ht hyEq hxEq
  have hexcess := excess_inequality he0 hdiff hx hy hq hr hbj hbl hid
  have hT : q * a * x + r * b * y ≤ 4 := by
    have h1 := (abs_le.mp (three_factor_bound hq ha0 ha1 hx)).2
    have h2 := (abs_le.mp (three_factor_bound hr hb0 hb1 hy)).2
    linarith only [h1, h2]
  have hP12 := coarse_excess_bound he0 hehalf hd hT hexcess
  have hfirst := refined_term_bound he0 hP0 ha0 ha1 hb0 hb1 hq hy htP hxEq
  have hsecond : r * b * y ≤ b * r ^ 2 + P + 2 * e := by
    apply refined_term_bound (y := -x) he0 hP0 hb0 hb1 ha0 ha1 hr
      (by simpa using hx) hsP
    linarith only [hyEq]
  have hTsharp : q * a * x + r * b * y ≤
      a * q ^ 2 + b * r ^ 2 + 2 * P + 4 * e := by linarith only [hfirst, hsecond]
  have hP32 := sharpen_excess_bound he0 hehalf hd hP0 hP12 hTsharp hexcess
  have hQ := mixed_quartic_bound ha hb hq hr hDl hDj
  have hP33 := final_excess_bound he0 hehalf hd hP32 hQ
  dsimp [P] at hP33
  nlinarith only [hP33, hsFail, htFail, he3]

end AngularCubic

end OAI
