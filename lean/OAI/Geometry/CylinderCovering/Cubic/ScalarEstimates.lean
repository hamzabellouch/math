import Mathlib

namespace OAI

namespace CubicBuffer

lemma abs_mul_le_of_bounds {a b A B : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)

lemma radial_difference_bound {s t P : ℝ}
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hP : P = s + t - 2) :
    0 ≤ P ∧ |s - t| ≤ P ∧ s ≤ 1 + P ∧ t ≤ 1 + P := by
  constructor
  · linarith
  constructor
  · rw [abs_le]
    constructor <;> linarith
  constructor <;> linarith

lemma coarse_excess_bound {ε P : ℝ}
    (he : 0 ≤ ε) (hehalf : ε ≤ 1 / 2)
    (h : P ≤ ε * P + 4 * ε ^ 2 + 4 * ε ^ 3) :
    P ≤ 12 * ε ^ 2 := by
  have he3 : ε ^ 3 ≤ ε ^ 2 / 2 := by
    nlinarith [mul_nonneg (pow_nonneg he 2) (sub_nonneg.mpr hehalf)]
  have hcoef : 1 / 2 ≤ 1 - ε := by linarith
  by_cases hP : P ≤ 0
  · nlinarith [sq_nonneg ε]
  · have hmul := mul_le_mul_of_nonneg_right hcoef (le_of_not_ge hP)
    nlinarith

lemma angular_polynomial_bound {a c q r Δ : ℝ}
    (ha : |a - (1 + r ^ 2) / 2| ≤ Δ)
    (hc : |c - (1 + q ^ 2) / 2| ≤ Δ)
    (hq : |q| ≤ 1) (hr : |r| ≤ 1) :
    a * q ^ 2 + c * r ^ 2 ≤
      (q ^ 2 + q ^ 4) / 2 + (r ^ 2 + r ^ 4) / 2 + 2 * Δ := by
  have hΔ : 0 ≤ Δ := le_trans (abs_nonneg _) ha
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [abs_le.mp hq, sq_abs q]
  have hr2 : r ^ 2 ≤ 1 := by nlinarith [abs_le.mp hr, sq_abs r]
  have ha' := (abs_le.mp ha).2
  have hc' := (abs_le.mp hc).2
  have hqa := mul_le_mul_of_nonneg_right ha' (sq_nonneg q)
  have hrc := mul_le_mul_of_nonneg_right hc' (sq_nonneg r)
  have hqΔ := mul_le_mul_of_nonneg_left hq2 hΔ
  have hrΔ := mul_le_mul_of_nonneg_left hr2 hΔ
  nlinarith [sq_nonneg (q ^ 2 - r ^ 2)]

lemma sharpened_excess_bound {ε Δ P A D : ℝ}
    (he : 0 ≤ ε) (hehalf : ε ≤ 1 / 2)
    (hΔ : 0 ≤ Δ) (hmesh : Δ ≤ ε ^ 2)
    (hPnonneg : 0 ≤ P) (hP : P ≤ 12 * ε ^ 2)
    (hA : A ≤ D + 2 * Δ)
    (h : P ≤ ε ^ 2 * A + ε * P + 2 * ε ^ 2 * P +
      4 * ε ^ 3 + 4 * ε * Δ) :
    P ≤ ε ^ 2 * D + 33 * ε ^ 3 := by
  have h1 : ε * P ≤ 12 * ε ^ 3 := by
    nlinarith [mul_le_mul (le_refl ε) hP hPnonneg he]
  have h2 : 2 * ε ^ 2 * P ≤ 12 * ε ^ 3 := by
    have hh : 2 * ε ^ 2 * P ≤ 24 * ε ^ 4 := by
      nlinarith [mul_le_mul_of_nonneg_left hP (sq_nonneg ε)]
    have hfour : 2 * ε ^ 4 ≤ ε ^ 3 := by
      have hc : 0 ≤ ε ^ 3 := pow_nonneg he 3
      nlinarith [mul_nonneg hc (sub_nonneg.mpr hehalf)]
    nlinarith
  have h3 : 4 * ε * Δ ≤ 4 * ε ^ 3 := by
    nlinarith [mul_le_mul (le_refl ε) hmesh hΔ he]
  have h4 : 2 * ε ^ 2 * Δ ≤ ε ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left hmesh (sq_nonneg ε)
    have hc : 0 ≤ ε ^ 3 := pow_nonneg he 3
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hehalf)]
  have h5 := mul_le_mul_of_nonneg_left hA (sq_nonneg ε)
  nlinarith

end CubicBuffer

end OAI
