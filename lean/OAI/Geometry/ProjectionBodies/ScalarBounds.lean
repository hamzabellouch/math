import OAI.Geometry.ProjectionBodies.NormCurvature

namespace OAI

noncomputable section
namespace PettyProjection.Scalar

def exponent (n : ℕ) : ℕ := if n = 4 then 1 else 2

def coefficient (n : ℕ) : ℝ :=
  if n = 4 then 121 / 35 else
    ((n : ℝ)^2 + 5 * n + 7) / (((n : ℝ) + 1) * ((n : ℝ) + 3))

def beta (n : ℕ) : ℝ := if n = 4 then 1 / 2 else 2 / 3

def weight (n : ℕ) : ℝ :=
  if n = 4 then 3 / 14 else if n = 5 ∨ n = 6 then 1 / 3 else 1 / 2

def e (n : ℕ) (z : ℝ) : ℝ := ((z⁻¹)^n - 1) / n

def M (n : ℕ) (z : ℝ) : ℝ := z ^ exponent n - 1 + exponent n * e n z

def W (n : ℕ) (z : ℝ) : ℝ := z ^ exponent n - z ^ (exponent n - 1) + e n z

def G (n : ℕ) (z : ℝ) : ℝ := if 1 < z then beta n * M n z else 0

def D (n : ℕ) (z : ℝ) : ℝ := z ^ exponent n - 1 - G n z

/-- Closed form of the integral of M'(a)^2 over [1,z], or zero below 1. -/
def I (n : ℕ) (z : ℝ) : ℝ :=
  if 1 < z then
    (exponent n : ℝ)^2 *
      ((z ^ (2 * exponent n - 1) - 1) / (2 * exponent n - 1 : ℕ) -
        2 * (1 - (z⁻¹) ^ (n + 1 - exponent n)) / (n + 1 - exponent n : ℕ) +
        (1 - (z⁻¹) ^ (2 * n + 1)) / (2 * n + 1 : ℕ))
  else 0

def L (n : ℕ) (z : ℝ) : ℝ :=
  coefficient n *
    ((((n : ℝ) - 1) * beta n ^ 2 * z * I n z - 2 * n * G n z ^ 2) /
        (weight n * (2 * n + 8)) + D n z ^ 2 / (1 - weight n))

/-- A second-order lower bound for inverse powers, valid in every dimension.
This is the low-z convexity estimate. -/
lemma inverse_pow_lower (n : ℕ) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    1 + n * (1 - z) + (n : ℝ) * (n + 1) / 2 * (1 - z)^2 ≤ (z⁻¹)^n := by
  have hx : 0 ≤ 1 - z := sub_nonneg.mpr hz1
  have hinv : 1 + (1 - z) + (1 - z)^2 ≤ z⁻¹ := by
    rw [← one_div z]
    apply (le_div_iff₀ hz).2
    nlinarith [mul_nonneg (sq_nonneg (1-z)) hx]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hprod := mul_le_mul ih hinv (by positivity : 0 ≤ 1 + (1-z) + (1-z)^2)
      (by positivity : 0 ≤ (z⁻¹)^n)
    push_cast
    calc
      1 + ((n : ℝ) + 1) * (1 - z) + ((n : ℝ) + 1) * ((n : ℝ) + 1 + 1) / 2 * (1 - z)^2
          ≤ (1 + (n : ℝ) * (1-z) + (n : ℝ) * (n+1) / 2 * (1-z)^2) *
            (1 + (1-z) + (1-z)^2) := by
              nlinarith [mul_nonneg (by positivity : 0 ≤ (n : ℝ))
                  (mul_nonneg (sq_nonneg (1-z)) hx),
                mul_nonneg (by positivity : 0 ≤ (n : ℝ) * (n+1) / 2)
                  (mul_nonneg (sq_nonneg (1-z)) hx),
                mul_nonneg (by positivity : 0 ≤ (n : ℝ) * (n+1) / 2)
                  (sq_nonneg ((1-z)^2))]
      _ ≤ _ := hprod

lemma coefficient_pos (n : ℕ) : 0 < coefficient n := by
  unfold coefficient
  split_ifs <;> positivity

lemma beta_pos (n : ℕ) : 0 < beta n := by
  unfold beta
  split_ifs <;> norm_num

lemma beta_lt_one (n : ℕ) : beta n < 1 := by
  unfold beta
  split_ifs <;> norm_num

lemma weight_pos (n : ℕ) : 0 < weight n := by
  unfold weight
  split_ifs <;> norm_num

lemma weight_lt_one (n : ℕ) : weight n < 1 := by
  unfold weight
  split_ifs <;> norm_num

/-- Exact positivity margin on the low-z interval in dimensions at least seven. -/
lemma large_local_margin {r : ℝ} (hr : 7 ≤ r) :
    0 < r + 3 - 8 * (r^2 + 5*r + 7) / ((r+1)*(r+3)) := by
  have hden : 0 < (r+1)*(r+3) := by positivity
  have ht : 0 ≤ r - 7 := by linarith
  have hpoly : 0 < r^3 - r^2 - 25*r - 47 := by
    have hcert : r^3-r^2-25*r-47 =
        (r-7)^3 + 20*(r-7)^2 + 108*(r-7) + 72 := by ring
    rw [hcert]
    positivity
  have heq : r+3-8*(r^2+5*r+7)/((r+1)*(r+3)) =
      (r^3-r^2-25*r-47)/((r+1)*(r+3)) := by
    field_simp
    ring
  rw [heq]
  exact div_pos hpoly hden

/-- Scalar mean bound, including every dimension. -/
lemma mean_bound (n : ℕ) (hn : 4 ≤ n) :
    coefficient n * (2*n*beta n^2 / (weight n * (2*n+8)) -
      (1-beta n)^2 / (1-weight n)) ≤
      (2*(exponent n : ℝ)-1) / (exponent n : ℝ)^2 := by
  by_cases h4 : n = 4
  · subst n
    norm_num [coefficient, beta, weight, exponent]
  by_cases h5 : n = 5
  · subst n
    norm_num [coefficient, beta, weight, exponent]
  by_cases h6 : n = 6
  · subst n
    norm_num [coefficient, beta, weight, exponent]
  have hn7 : 7 ≤ n := by omega
  have hr : 7 ≤ (n : ℝ) := by exact_mod_cast hn7
  simp only [coefficient, beta, weight, exponent, h4, h5, h6,
    ite_false, or_self, Nat.cast_ofNat]
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
  have h4' : (n : ℝ) + 4 ≠ 0 := by positivity
  have hd : 0 < 36*((n : ℝ)+1)*(n+3)*(n+4) := by positivity
  have hcert : 3/4 - ( ((n : ℝ)^2+5*n+7) / ((n+1)*(n+3)) *
      (2*n*(2/3)^2 / (1/2*(2*n+8)) - (1-2/3)^2/(1-1/2))) =
      (3*(n : ℝ)^3+128*n^2+505*n+548) / (36*(n+1)*(n+3)*(n+4)) := by
    field_simp
    ring
  have hpos : 0 < 3*(n : ℝ)^3+128*n^2+505*n+548 := by positivity
  have := div_pos hpos hd
  rw [← hcert] at this
  norm_num only [OfNat.ofNat_ne_zero, Nat.reduceAdd, Nat.reduceMul] at *
  linarith

lemma local_margin (n : ℕ) (hn : 4 ≤ n) :
    coefficient n * (exponent n : ℝ)^2 / (1 - weight n) <
      n + 2 * (exponent n : ℝ) - 1 := by
  by_cases h4 : n = 4
  · subst n
    norm_num [coefficient, weight, exponent]
  by_cases h5 : n = 5
  · subst n
    norm_num [coefficient, weight, exponent]
  by_cases h6 : n = 6
  · subst n
    norm_num [coefficient, weight, exponent]
  have hn7 : 7 ≤ n := by omega
  have hr : 7 ≤ (n : ℝ) := by exact_mod_cast hn7
  have h := large_local_margin hr
  simp only [coefficient, weight, exponent, h4, h5, h6, ite_false, or_self,
    Nat.cast_ofNat]
  convert (sub_pos.mp h) using 1 <;> ring

lemma low_W_bound (n : ℕ) (hn : 4 ≤ n) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    (n + 2 * (exponent n : ℝ) - 1) * (z-1)^2 ≤ 2 * W n z := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp := inverse_pow_lower n hz hz1
  have he : -(z-1) + ((n : ℝ)+1)/2 * (z-1)^2 ≤ e n z := by
    unfold e
    apply (le_div_iff₀ hn0).2
    nlinarith [hp]
  by_cases h4 : n = 4
  · subst n
    norm_num only [W, exponent, ite_true, pow_one, Nat.reduceSub, pow_zero,
      Nat.cast_one, Nat.cast_ofNat] at ⊢ he
    nlinarith
  · simp only [W, exponent, h4, ite_false, Nat.reduceSub, pow_one, Nat.cast_ofNat]
    nlinarith

lemma low_D_square (n : ℕ) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    (z ^ exponent n - 1)^2 ≤ (exponent n : ℝ)^2 * (z-1)^2 := by
  by_cases h4 : n = 4
  · simp [exponent, h4]
  · simp only [exponent, h4, ite_false, Nat.cast_ofNat]
    have hs : (z+1)^2 ≤ 4 := by nlinarith
    have := mul_le_mul_of_nonneg_left hs (sq_nonneg (z-1))
    nlinarith

lemma low_pointwise (n : ℕ) (hn : 4 ≤ n) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    L n z ≤ 2 * W n z ∧ (L n z = 2 * W n z ↔ z = 1) := by
  have hnot : ¬ 1 < z := not_lt.mpr hz1
  have hwt : 0 < 1 - weight n := sub_pos.mpr (weight_lt_one n)
  have hc : 0 < coefficient n / (1-weight n) := div_pos (coefficient_pos n) hwt
  have hL : L n z = coefficient n / (1-weight n) * (z ^ exponent n - 1)^2 := by
    simp [L, D, G, I, hnot, div_mul_eq_mul_div]
    ring
  by_cases heq : z = 1
  · subst z
    simp [L, G, I, D, W, e]
  have hsq : 0 < (z-1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr heq)
  have hlt : L n z < 2 * W n z := calc
    L n z = coefficient n / (1-weight n) * (z ^ exponent n - 1)^2 := hL
    _ ≤ coefficient n / (1-weight n) * ((exponent n : ℝ)^2 * (z-1)^2) :=
      mul_le_mul_of_nonneg_left (low_D_square n hz hz1) hc.le
    _ = (coefficient n * (exponent n : ℝ)^2 / (1-weight n)) * (z-1)^2 := by ring
    _ < (n + 2 * (exponent n : ℝ) - 1) * (z-1)^2 :=
      mul_lt_mul_of_pos_right (local_margin n hn) hsq
    _ ≤ 2 * W n z := low_W_bound n hn hz hz1
  exact ⟨hlt.le, iff_of_false (ne_of_lt hlt) heq⟩

def P4 (z : ℝ) : ℝ := 462 * z^10 - 983 * z^9 + 93 * z^8 + 3399 * z^5 - 3378 * z^4 + 407

lemma certificate_4 {z : ℝ} (hz : 1 < z) :
    2880 * z^8 * (2 * W 4 z - L 4 z) = P4 z := by
  have hz0 : z ≠ 0 := by linarith
  simp only [W, L, D, G, I, M, e, exponent, coefficient, weight, beta, P4]
  norm_num [hz]
  field_simp
  ring

def U4 (x : ℝ) : ℝ := 17052 * x^4 - 6711 * x^2 - 1446 * x + 1728

lemma U4_pos (x : ℝ) : 0 < U4 x := by
  have h1 : 1446*x ≤ 400 + 1400*x^2 := by
    nlinarith [sq_nonneg (2800*x-1446)]
  have h2 : 8111*x^2 ≤ 1000 + 17052*x^4 := by
    nlinarith [sq_nonneg (34104*x^2-8111)]
  dsimp [U4]
  linarith

lemma P4_pos {z : ℝ} (hz : 1 < z) : 0 < P4 z := by
  let x := z-1
  have hx : 0 < x := sub_pos.mpr hz
  have heq : P4 z = x^2 * (U4 x + (462 * x^8 + 3637 * x^7 + 12036 * x^6 + 20796 * x^5 + 1173 * x^3)) := by
    dsimp [P4, U4, x]
    ring
  rw [heq]
  have hu := U4_pos x
  positivity

lemma high_pointwise_4 {z : ℝ} (hz : 1 < z) : L 4 z < 2 * W 4 z := by
  have h := P4_pos hz
  rw [← certificate_4 hz] at h
  have hp : 0 < (2880 : ℝ) * z^8 := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp h)

def P5 (z : ℝ) : ℝ := 151525 * z^14 - 273570 * z^12 - 680800 * z^11 + 938157 * z^10 + 225720 * z^7 - 462264 * z^5 + 101232

lemma certificate_5 {z : ℝ} (hz : 1 < z) :
    712800 * z^10 * (2 * W 5 z - L 5 z) = P5 z := by
  have hz0 : z ≠ 0 := by linarith
  simp only [W, L, D, G, I, M, e, exponent, coefficient, weight, beta, P5]
  norm_num [hz]
  field_simp
  ring

def U5 (x : ℝ) : ℝ := 86314305 * x^4 - 5802775 * x^2 - 1505900 * x + 623700

lemma U5_pos (x : ℝ) : 0 < U5 x := by
  have h1 : 1505900*x ≤ 200000 + 2900000*x^2 := by
    nlinarith [sq_nonneg (5800000*x-1505900)]
  have h2 : 8702775*x^2 ≤ 230000 + 86314305*x^4 := by
    nlinarith [sq_nonneg (172628610*x^2-8702775)]
  dsimp [U5]
  linarith

lemma P5_pos {z : ℝ} (hz : 1 < z) : 0 < P5 z := by
  let x := z-1
  have hx : 0 < x := sub_pos.mpr hz
  have heq : P5 z = x^2 * (U5 x + (151525 * x^12 + 2121350 * x^11 + 13515205 * x^10 + 51191460 * x^9 + 127070262 * x^8 + 215105220 * x^7 + 249497490 * x^6 + 191506920 * x^5 + 12849430 * x^3)) := by
    dsimp [P5, U5, x]
    ring
  rw [heq]
  have hu := U5_pos x
  positivity

lemma high_pointwise_5 {z : ℝ} (hz : 1 < z) : L 5 z < 2 * W 5 z := by
  have h := P5_pos hz
  rw [← certificate_5 hz] at h
  have hp : 0 < (712800 : ℝ) * z^10 := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp h)

def P6 (z : ℝ) : ℝ := 48399 * z^16 - 75894 * z^14 - 218004 * z^13 + 285961 * z^12 + 56940 * z^8 - 127478 * z^6 + 30076

lemma certificate_6 {z : ℝ} (hz : 1 < z) :
    221130 * z^12 * (2 * W 6 z - L 6 z) = P6 z := by
  have hz0 : z ≠ 0 := by linarith
  simp only [W, L, D, G, I, M, e, exponent, coefficient, weight, beta, P6]
  norm_num [hz]
  field_simp
  ring

def U6 (x : ℝ) : ℝ := 51269452 * x^4 - 132249 * x^2 + 452790

lemma U6_pos (x : ℝ) : 0 < U6 x := by
  dsimp [U6]
  nlinarith [sq_nonneg (102538904*x^2-132249)]

lemma P6_pos {z : ℝ} (hz : 1 < z) : 0 < P6 z := by
  let x := z-1
  have hx : 0 < x := sub_pos.mpr hz
  have heq : P6 z = x^2 * (U6 x + (48399 * x^14 + 774384 * x^13 + 5731986 * x^12 + 25822920 * x^11 + 78631735 * x^10 + 170208636 * x^9 + 268133580 * x^8 + 308783332 * x^7 + 256021935 * x^6 + 146058120 * x^5 + 7800780 * x^3 + 679380 * x)) := by
    dsimp [P6, U6, x]
    ring
  rw [heq]
  have hu := U6_pos x
  positivity

lemma high_pointwise_6 {z : ℝ} (hz : 1 < z) : L 6 z < 2 * W 6 z := by
  have h := P6_pos hz
  rw [← certificate_6 hz] at h
  have hp : 0 < (221130 : ℝ) * z^12 := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp h)

def P7 (z : ℝ) : ℝ := 3185 * z^18 + 77910 * z^16 - 185472 * z^15 + 101385 * z^14 + 40040 * z^9 - 43080 * z^7 + 6032

lemma certificate_7 {z : ℝ} (hz : 1 < z) :
    138600 * z^14 * (2 * W 7 z - L 7 z) = P7 z := by
  have hz0 : z ≠ 0 := by linarith
  simp only [W, L, D, G, I, M, e, exponent, coefficient, weight, beta, P7]
  norm_num [hz]
  field_simp
  ring

lemma P7_pos {z : ℝ} (hz : 1 < z) : 0 < P7 z := by
  let x := z-1
  have hx : 0 < x := sub_pos.mpr hz
  have heq : P7 z = x^2 * (3185 * x^16 + 57330 * x^15 + 565215 * x^14 + 3660048 * x^13 + 16414605 * x^12 + 52863510 * x^11 + 125758815 * x^10 + 225405180 * x^9 + 307786479 * x^8 + 320870550 * x^7 + 253378125 * x^6 + 148489200 * x^5 + 62263215 * x^4 + 17740674 * x^3 + 3396645 * x^2 + 598500 * x + 124740) := by
    dsimp [P7, x]
    ring
  rw [heq]
  positivity

lemma high_pointwise_7 {z : ℝ} (hz : 1 < z) : L 7 z < 2 * W 7 z := by
  have h := P7_pos hz
  rw [← certificate_7 hz] at h
  have hp : 0 < (138600 : ℝ) * z^14 := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp h)

def P8 (z : ℝ) : ℝ := 5032 * z^20 + 106896 * z^18 - 245128 * z^17 + 131937 * z^16 + 45288 * z^10 - 52683 * z^8 + 8658

lemma certificate_8 {z : ℝ} (hz : 1 < z) :
    181764 * z^16 * (2 * W 8 z - L 8 z) = P8 z := by
  have hz0 : z ≠ 0 := by linarith
  simp only [W, L, D, G, I, M, e, exponent, coefficient, weight, beta, P8]
  norm_num [hz]
  field_simp
  ring

lemma P8_pos {z : ℝ} (hz : 1 < z) : 0 < P8 z := by
  let x := z-1
  have hx : 0 < x := sub_pos.mpr hz
  have heq : P8 z = x^2 * (5032 * x^18 + 100640 * x^17 + 1062976 * x^16 + 7415480 * x^15 + 36699889 * x^14 + 134016848 * x^13 + 371287480 * x^12 + 796445648 * x^11 + 1341571660 * x^10 + 1789629712 * x^9 + 1896594800 * x^8 + 1593208720 * x^7 + 1052388995 * x^6 + 539061976 * x^5 + 210340388 * x^4 + 61812136 * x^3 + 14025170 * x^2 + 2645608 * x + 369036) := by
    dsimp [P8, x]
    ring
  rw [heq]
  positivity

lemma high_pointwise_8 {z : ℝ} (hz : 1 < z) : L 8 z < 2 * W 8 z := by
  have h := P8_pos hz
  rw [← certificate_8 hz] at h
  have hp : 0 < (181764 : ℝ) * z^16 := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp h)

def P9 (z : ℝ) : ℝ := 17955 * z^22 + 344826 * z^20 - 771336 * z^19 + 409763 * z^18 + 124488 * z^11 - 153472 * z^9 + 27776

lemma certificate_9 {z : ℝ} (hz : 1 < z) :
    568620 * z^18 * (2 * W 9 z - L 9 z) = P9 z := by
  have hz0 : z ≠ 0 := by linarith
  simp only [W, L, D, G, I, M, e, exponent, coefficient, weight, beta, P9]
  norm_num [hz]
  field_simp
  ring

lemma P9_pos {z : ℝ} (hz : 1 < z) : 0 < P9 z := by
  let x := z-1
  have hx : 0 < x := sub_pos.mpr hz
  have heq : P9 z = x^2 * (17955 * x^20 + 395010 * x^19 + 4492431 * x^18 + 33775884 * x^17 + 182612144 * x^16 + 741405888 * x^15 + 2325627540 * x^14 + 5752968096 * x^13 + 11391705882 * x^12 + 18245048652 * x^11 + 23789022114 * x^10 + 25324311168 * x^9 + 21996503100 * x^8 + 15523044480 * x^7 + 8829652644 * x^6 + 4002804432 * x^5 + 1428705963 * x^4 + 398939634 * x^3 + 87942807 * x^2 + 15343236 * x + 1781676) := by
    dsimp [P9, x]
    ring
  rw [heq]
  positivity

lemma high_pointwise_9 {z : ℝ} (hz : 1 < z) : L 9 z < 2 * W 9 z := by
  have h := P9_pos hz
  rw [← certificate_9 hz] at h
  have hp : 0 < (568620 : ℝ) * z^18 := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp h)

open Finset

/-- The exact coefficient comparison used in the all-dimensional scalar estimate. -/
lemma choose_double (n j : ℕ) : 2^j * n.choose j ≤ (2*n).choose j := by
  induction n generalizing j with
  | zero => cases j <;> simp
  | succ n ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [Nat.choose_succ_succ]
      calc
        2^(j+1)*(n.choose j + n.choose (j+1)) =
            2*(2^j*n.choose j) + 2^(j+1)*n.choose (j+1) := by ring
        _ ≤ 2*(2*n).choose j + (2*n).choose (j+1) :=
          Nat.add_le_add (Nat.mul_le_mul_left 2 (ih j)) (ih (j+1))
        _ ≤ (2*(n+1)).choose (j+1) := by
          have hh := Nat.choose_le_succ (2*n) j
          have heq : 2*(n+1) = (2*n+1)+1 := by omega
          rw [heq, Nat.choose_succ_succ, Nat.choose_succ_succ]
          simp only [Nat.succ_eq_add_one] at hh ⊢
          omega

lemma choose_double_cubic {n j : ℕ} (hj : 3 ≤ j) :
    8 * (n.choose j : ℝ) ≤ ((2*n).choose j : ℝ) := by
  have hp : 8 ≤ 2^j := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hj
    norm_num at this ⊢
    exact this
  exact_mod_cast le_trans (Nat.mul_le_mul_right (n.choose j) hp) (choose_double n j)

/-- Taylor remainder of the n-th power after its quadratic term. -/
def tail (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (n+1), if 3 ≤ j then (n.choose j : ℝ)*x^j else 0

lemma tail_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ tail n x := by
  apply sum_nonneg
  intro j _
  split_ifs <;> positivity

lemma tail_expansion (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    (1+x)^n = 1 + n*x + (n.choose 2 : ℝ)*x^2 + tail n x := by
  have heq : n+1 = 3 + (n-2) := by omega
  have hp := add_pow x (1:ℝ) n
  simp only [one_pow,mul_one] at hp
  rw [add_comm] at hp
  rw [hp]
  simp only [tail]
  rw [heq, sum_range_add, sum_range_add]
  have hsum : (∑ j ∈ range (n-2), x^(3+j)*(n.choose (3+j) : ℝ)) =
      ∑ j ∈ range (n-2), if 3 ≤ 3+j then (n.choose (3+j) : ℝ)*x^(3+j) else 0 := by
    apply sum_congr rfl
    intro j _
    simp [mul_comm]
  rw [hsum]
  norm_num [sum_range_succ, Nat.choose_one_right]
  ring

lemma tail_double (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    8 * tail n x ≤ tail (2*n) x := by
  let f : ℕ → ℝ := fun j => if 3 ≤ j then (n.choose j : ℝ)*x^j else 0
  have hzero : ∀ j, n+1 ≤ j → f j = 0 := by
    intro j hj
    unfold f
    rw [Nat.choose_eq_zero_of_lt (by omega : n < j)]
    simp
  have hext : tail n x = ∑ j ∈ range (2*n+1), f j := by
    change (∑ j ∈ range (n+1), f j) = _
    have heq : 2*n+1 = (n+1)+n := by omega
    rw [heq, sum_range_add (f := f) (n+1) n]
    have : ∑ j ∈ range n, f (n+1+j) = 0 := by
      apply sum_eq_zero
      intro j _
      exact hzero _ (by omega)
    change (∑ j ∈ range (n+1), f j) = _
    rw [this,add_zero]
  rw [hext, mul_sum]
  unfold tail
  apply sum_le_sum
  intro j _
  dsimp [f]
  split_ifs with hj
  · have h := mul_le_mul_of_nonneg_right (choose_double_cubic (n:=n) hj)
      (pow_nonneg hx j)
    nlinarith only [h]
  · simp

/-- Positivity mechanism for the all-dimensional polynomial.
Cancellation of its first two coefficients leaves a positive quadratic term;
all later coefficients are controlled by the doubled binomial comparison. -/
lemma shifted_polynomial_pos (n : ℕ) (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x)
    (a b c d e u v w t : ℝ)
    (hzero : a+u+t=0) (hone : 2*n*a+b+n*u+v=0)
    (htwo : 0 < ((2*n).choose 2 : ℝ)*a+2*n*b+c+(n.choose 2 : ℝ)*u+n*v+w)
    (ha : 0 ≤ a) (hau : 0 ≤ 8*a+u)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hv : 0 ≤ v) (hw : 0 ≤ w) :
    0 < (1+x)^(2*n)*(a+b*x+c*x^2+d*x^3+e*x^4)+
      (1+x)^n*(u+v*x+w*x^2)+t := by
  have htn := tail_nonneg n hx.le
  have ht2n := tail_nonneg (2*n) hx.le
  have hdouble : 0 ≤ tail (2*n) x - 8*tail n x := sub_nonneg.mpr (tail_double n hx.le)
  have hmain : 0 < (((2*n).choose 2 : ℝ)*a+2*n*b+c+(n.choose 2 : ℝ)*u+n*v+w)*x^2 :=
    mul_pos htwo (sq_pos_of_pos hx)
  have hrest : 0 ≤
      a*(tail (2*n) x-8*tail n x) + (8*a+u)*tail n x +
      b*x*(((2*n).choose 2 : ℝ)*x^2+tail (2*n) x) +
      c*x^2*(2*n*x+((2*n).choose 2 : ℝ)*x^2+tail (2*n) x) +
      d*x^3*(1+x)^(2*n) + e*x^4*(1+x)^(2*n) +
      v*x*((n.choose 2 : ℝ)*x^2+tail n x) +
      w*x^2*(n*x+(n.choose 2 : ℝ)*x^2+tail n x) := by positivity
  have hidentity : (1+x)^(2*n)*(a+b*x+c*x^2+d*x^3+e*x^4)+
      (1+x)^n*(u+v*x+w*x^2)+t =
      (((2*n).choose 2 : ℝ)*a+2*n*b+c+(n.choose 2 : ℝ)*u+n*v+w)*x^2 +
      (a*(tail (2*n) x-8*tail n x) + (8*a+u)*tail n x +
      b*x*(((2*n).choose 2 : ℝ)*x^2+tail (2*n) x) +
      c*x^2*(2*n*x+((2*n).choose 2 : ℝ)*x^2+tail (2*n) x) +
      d*x^3*(1+x)^(2*n) + e*x^4*(1+x)^(2*n) +
      v*x*((n.choose 2 : ℝ)*x^2+tail n x) +
      w*x^2*(n*x+(n.choose 2 : ℝ)*x^2+tail n x)) := by
    rw [tail_expansion n hn x, tail_expansion (2*n) (by omega) x]
    have ht : t = -a-u := by linarith
    have hb' : b = -2*n*a-n*u-v := by linarith
    rw [ht, hb']
    push_cast
    ring
  rw [hidentity]
  exact add_pos_of_pos_of_nonneg hmain hrest

def largeC (r : ℝ) := (r^2+5*r+7)/((r+1)*(r+3))
def H (r : ℝ) := 18*(r+4)/largeC r

def A4 (r : ℝ) := (2*r-8)/3
def A2 (r : ℝ) := H r-12*r-32-64/r
def A1 (r : ℝ) := -H r+16*(r-1)/3+32-16*(r-1)/(2*r+1)
def A0 (r : ℝ) := -H r/r+6*r+40+64/r-128/r^2
def B2 (r : ℝ) := 16+64/r
def B0 (r : ℝ) := H r/r-48-64/r+256/r^2
def T0 (r : ℝ) := 16*(r-1)/(2*r+1)-128/r^2

def q0 (r : ℝ) := A4 r+A2 r+A1 r+A0 r
def q1 (r : ℝ) := 4*A4 r+2*A2 r+A1 r
def q2 (r : ℝ) := 6*A4 r+A2 r
def q3 (r : ℝ) := 4*A4 r
def q4 (r : ℝ) := A4 r
def r0 (r : ℝ) := B2 r+B0 r
def r1 (r : ℝ) := 2*B2 r
def r2 (r : ℝ) := B2 r

def V0 (r : ℝ) := 34*r^5-95*r^4-1666*r^3-5701*r^2-8052*r-2688
def V1 (r : ℝ) := 2*r^5+9*r^4-162*r^3-845*r^2-1220*r-448
def V2 (r : ℝ) := 5*r^3+8*r^2-41*r-56
def R0 (r : ℝ) := 7*r^4+8*r^3-187*r^2-748*r-896

lemma V0_pos {r : ℝ} (hr : 10 ≤ r) : 0 < V0 r := by
  have ht : 0 ≤ r-10 := by linarith
  have heq : V0 r = 34*(r-10)^5+1605*(r-10)^4+28534*(r-10)^3+
      227319*(r-10)^2+698128*(r-10)+130692 := by unfold V0; ring
  rw [heq]
  positivity

lemma V1_pos {r : ℝ} (hr : 10 ≤ r) : 0 < V1 r := by
  have ht : 0 ≤ r-10 := by linarith
  have heq : V1 r = 2*(r-10)^5+109*(r-10)^4+2198*(r-10)^3+
      19695*(r-10)^2+69280*(r-10)+30852 := by unfold V1; ring
  rw [heq]
  positivity

lemma V2_pos {r : ℝ} (hr : 7 ≤ r) : 0 < V2 r := by
  have ht : 0 ≤ r-7 := by linarith
  have heq : V2 r = 5*(r-7)^3+113*(r-7)^2+806*(r-7)+1764 := by unfold V2; ring
  rw [heq]
  positivity

lemma R0_pos {r : ℝ} (hr : 7 ≤ r) : 0 < R0 r := by
  have ht : 0 ≤ r-7 := by linarith
  have heq : R0 r = 7*(r-7)^4+204*(r-7)^3+2039*(r-7)^2+7414*(r-7)+4256 := by
    unfold R0
    ring
  rw [heq]
  positivity

lemma q0_identity {r : ℝ} (hr : 0 < r) :
    q0 r+r0 r/8 = V0 r/(4*r^2*(2*r+1)*(r^2+5*r+7)) := by
  unfold q0 r0 A4 A2 A1 A0 B2 B0 H largeC V0
  field_simp
  ring

lemma q1_identity {r : ℝ} (hr : 0 < r) :
    q1 r = 2*V1 r/(r*(2*r+1)*(r^2+5*r+7)) := by
  unfold q1 A4 A2 A1 H largeC V1
  field_simp
  ring

lemma q2_identity {r : ℝ} (hr : 0 < r) :
    q2 r = 2*(r+4)*V2 r/(r*(r^2+5*r+7)) := by
  unfold q2 A4 A2 H largeC V2
  field_simp
  ring

lemma r0_identity {r : ℝ} (hr : 0 < r) :
    r0 r = -2*R0 r/(r^2*(r^2+5*r+7)) := by
  unfold r0 B2 B0 H largeC R0
  field_simp
  ring

lemma large_signs {r : ℝ} (hr : 10 ≤ r) :
    0 < q0 r ∧ 0 < 8*q0 r+r0 r ∧ 0 < q1 r ∧ 0 < q2 r ∧
    0 < q3 r ∧ 0 < q4 r ∧ 0 < r1 r ∧ 0 < r2 r := by
  have hr0 : 0 < r := by linarith
  have hr7 : 7 ≤ r := by linarith
  have hs : 0 < q0 r+r0 r/8 := by
    rw [q0_identity hr0]
    exact div_pos (V0_pos hr) (by positivity)
  have hneg : r0 r < 0 := by
    rw [r0_identity hr0]
    exact div_neg_of_neg_of_pos (by nlinarith [R0_pos hr7]) (by positivity)
  have h8 : 0 < 2*r-8 := by linarith
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [q1_identity hr0]
    exact div_pos (mul_pos (by norm_num) (V1_pos hr)) (by positivity)
  · rw [q2_identity hr0]
    exact div_pos (mul_pos (by positivity) (V2_pos hr7)) (by positivity)
  · unfold q3 A4
    positivity
  · unfold q4 A4
    positivity
  · unfold r1 B2
    positivity
  · unfold r2 B2
    positivity

lemma constant_vanish {r : ℝ} (hr : 0 < r) : q0 r + r0 r + T0 r = 0 := by
  unfold q0 r0 A4 A2 A1 A0 B2 B0 T0 H largeC
  field_simp
  ring

lemma linear_vanish {r : ℝ} (hr : 0 < r) :
    2*r*q0 r + q1 r + r*r0 r + r1 r = 0 := by
  unfold q0 q1 r0 r1 A4 A2 A1 A0 B2 B0 H largeC
  field_simp
  ring

lemma quadratic_identity {r : ℝ} (hr : 0 < r) :
    r*(2*r-1)*q0 r + 2*r*q1 r + q2 r + r*(r-1)/2*r0 r+r*r1 r+r2 r =
      9*(r+4)/largeC r*(r+3-8*largeC r) := by
  unfold q0 q1 q2 r0 r1 r2 A4 A2 A1 A0 B2 B0 H largeC
  field_simp
  ring

lemma large_polynomial_pos (n : ℕ) (hn : 10 ≤ n) {z : ℝ} (hz : 1 < z) :
    0 < z^(2*n)*(A4 n*z^4+A2 n*z^2+A1 n*z+A0 n)+
      z^n*(B2 n*z^2+B0 n)+T0 n := by
  have hr : 10 ≤ (n : ℝ) := by exact_mod_cast hn
  have hr0 : 0 < (n : ℝ) := by linarith
  obtain ⟨hq0,hq0r0,hq1,hq2,hq3,hq4,hr1,hr2⟩ := large_signs hr
  have hc : 0 < largeC n := by unfold largeC; positivity
  have hmargin : 0 < (n : ℝ)+3-8*largeC n := by
    have hm := large_local_margin (r := (n : ℝ)) (by linarith)
    unfold largeC
    convert hm using 1; ring
  have htwo : 0 < (((2*n).choose 2 : ℕ) : ℝ)*q0 n+2*n*q1 n+q2 n+
      (n.choose 2 : ℝ)*r0 n+n*r1 n+r2 n := by
    rw [Nat.cast_choose_two ℝ, Nat.cast_choose_two ℝ]
    push_cast
    have heq : (2*(n:ℝ)*(2*n-1)/2*q0 n+2*n*q1 n+q2 n+
        n*(n-1)/2*r0 n+n*r1 n+r2 n) =
        9*(n+4)/largeC n*(n+3-8*largeC n) := by
      convert quadratic_identity hr0 using 1; ring
    rw [heq]
    positivity
  have hh := shifted_polynomial_pos n (by omega) (sub_pos.mpr hz)
    (q0 n) (q1 n) (q2 n) (q3 n) (q4 n) (r0 n) (r1 n) (r2 n) (T0 n)
    (constant_vanish hr0) (linear_vanish hr0) htwo hq0.le hq0r0.le
    hq1.le hq2.le hq3.le hq4.le hr1.le hr2.le
  have heq : z^(2*n)*(A4 n*z^4+A2 n*z^2+A1 n*z+A0 n)+
      z^n*(B2 n*z^2+B0 n)+T0 n =
      (1+(z-1))^(2*n)*(q0 n+q1 n*(z-1)+q2 n*(z-1)^2+q3 n*(z-1)^3+q4 n*(z-1)^4)+
      (1+(z-1))^n*(r0 n+r1 n*(z-1)+r2 n*(z-1)^2)+T0 n := by
    rw [show 1+(z-1)=z by ring]
    unfold q0 q1 q2 q3 q4 r0 r1 r2
    ring
  rw [heq]
  exact hh

lemma z_mul_inverse_pow_succ {z : ℝ} (hz : z ≠ 0) (m : ℕ) :
    z*(z⁻¹)^(m+1) = (z⁻¹)^m := by
  rw [pow_succ', ← mul_assoc, mul_inv_cancel₀ hz, one_mul]

lemma large_I_formula (n : ℕ) (hn : 7 ≤ n) {z : ℝ} (hz : 1 < z) :
    z*I n z = 4*((z^4-z)/3 - 2*(z-z^2*(z⁻¹)^n)/((n:ℝ)-1) +
      (z-((z⁻¹)^n)^2)/(2*n+1)) := by
  have h4 : n ≠ 4 := by omega
  have hz0 : z ≠ 0 := by linarith
  have hp : (z⁻¹)^(n+1-2) = z*(z⁻¹)^n := by
    have hv := z_mul_inverse_pow_succ hz0 (n+1-2)
    have he : n+1-2+1=n := by omega
    rw [he] at hv
    exact hv.symm
  have hd : z*(z⁻¹)^(2*n+1) = ((z⁻¹)^n)^2 := by
    rw [z_mul_inverse_pow_succ hz0, show 2*n=n*2 by omega, pow_mul]
  have hcast : ((n+1-2 : ℕ) : ℝ) = (n:ℝ)-1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_add]
    norm_num
    ring
  simp only [I, exponent, h4, ite_false, hz, ite_true, Nat.cast_ofNat,
    Nat.reduceMul, Nat.reduceSub, Nat.cast_add, Nat.cast_mul, Nat.cast_one, hcast]
  rw [hp]
  have hr1 : (n:ℝ)-1 ≠ 0 := by
    have hr : 7 ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hr2 : 2*(n:ℝ)+1 ≠ 0 := by positivity
  field_simp
  simp only [inv_eq_one_div] at hd
  linear_combination -12 * ((n : ℝ) - 1) * hd

lemma large_gap_formula (n : ℕ) (hn : 7 ≤ n) {z : ℝ} (hz : 1 < z) :
    9*((n:ℝ)+4)/coefficient n*(2*W n z-L n z) =
      A4 n*z^4+A2 n*z^2+A1 n*z+A0 n+
      (z⁻¹)^n*(B2 n*z^2+B0 n)+((z⁻¹)^n)^2*T0 n := by
  have h4 : n ≠ 4 := by omega
  have h56 : ¬(n=5 ∨ n=6) := by omega
  have hr : 7 ≤ (n:ℝ) := by exact_mod_cast hn
  have hr0 : 0 < (n:ℝ) := by linarith
  have hc : coefficient n = largeC n := by
    simp [coefficient, largeC, h4]
  have hc0 : largeC n ≠ 0 := by
    unfold largeC
    positivity
  have hI := large_I_formula n hn hz
  unfold L
  simp only [W, D, G, M, e, exponent, beta, weight, h4, h56, ite_false, hz,
    ite_true, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [hc]
  have heq : ((n:ℝ)-1)*(2/3)^2*z*I n z = ((n:ℝ)-1)*(2/3)^2*(z*I n z) := by ring
  rw [heq, hI]
  have hr1 : (n:ℝ)-1 ≠ 0 := by linarith
  unfold A4 A2 A1 A0 B2 B0 T0 H largeC
  field_simp [hr1]
  ring

lemma large_cleared_gap (n : ℕ) (hn : 7 ≤ n) {z : ℝ} (hz : 1 < z) :
    9*((n:ℝ)+4)/coefficient n*z^(2*n)*(2*W n z-L n z) =
      z^(2*n)*(A4 n*z^4+A2 n*z^2+A1 n*z+A0 n)+
      z^n*(B2 n*z^2+B0 n)+T0 n := by
  have hz0 : z ≠ 0 := by linarith
  have hzpow : z^n ≠ 0 := pow_ne_zero n hz0
  calc
    _ = z^(2*n)*(9*((n:ℝ)+4)/coefficient n*(2*W n z-L n z)) := by ring
    _ = _ := by
      rw [large_gap_formula n hn hz, show 2*n=n*2 by omega, pow_mul, inv_pow]
      field_simp

lemma high_pointwise_large (n : ℕ) (hn : 10 ≤ n) {z : ℝ} (hz : 1 < z) :
    L n z < 2*W n z := by
  have hp := large_polynomial_pos n hn hz
  rw [← large_cleared_gap n (by omega) hz] at hp
  have hc : 0 < 9*((n:ℝ)+4)/coefficient n*z^(2*n) := by
    have hc := coefficient_pos n
    positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hc).mp hp)

/-- The pointwise scalar estimate, including its exact equality
condition, in every dimension covered by the main theorem. -/
theorem pointwise (n : ℕ) (hn : 4 ≤ n) {z : ℝ} (hz : 0 < z) :
    L n z ≤ 2*W n z ∧ (L n z = 2*W n z ↔ z=1) := by
  by_cases hz1 : z ≤ 1
  · exact low_pointwise n hn hz hz1
  have hz' : 1 < z := lt_of_not_ge hz1
  have hlt : L n z < 2*W n z := by
    by_cases hn10 : 10 ≤ n
    · exact high_pointwise_large n hn10 hz'
    interval_cases n
    · exact high_pointwise_4 hz'
    · exact high_pointwise_5 hz'
    · exact high_pointwise_6 hz'
    · exact high_pointwise_7 hz'
    · exact high_pointwise_8 hz'
    · exact high_pointwise_9 hz'
  exact ⟨hlt.le, iff_of_false (ne_of_lt hlt) (ne_of_gt hz')⟩

end PettyProjection.Scalar
end

end OAI
