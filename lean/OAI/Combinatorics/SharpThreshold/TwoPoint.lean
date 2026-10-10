import Mathlib

namespace OAI

noncomputable section

namespace Problem313

/-- A pointwise fourth-power estimate with the linear term retained for averaging. -/
lemma fourth_power_centered_bound (a z : ℝ) :
    (a + z) ^ 4 ≤ a ^ 4 + 4 * a ^ 3 * z + 8 * a ^ 2 * z ^ 2 + 3 * z ^ 4 := by
  nlinarith only [sq_nonneg (z * (a - z))]

/-- The scalar two-point estimate used to tensorize biased hypercontractivity.
The noise parameter is `sqrt (p * (1-p)) / 4`; after cancellation of the
normalization in the biased character, its two values are `-p / 4` and
`(1-p) / 4`. This formulation also includes the endpoint biases. -/
theorem biased_two_point_fourth_moment (p a b : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * (a - p * b / 4) ^ 4 + p * (a + (1 - p) * b / 4) ^ 4 ≤
      (a ^ 2 + b ^ 2) ^ 2 := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have h1 := fourth_power_centered_bound a (-p * b / 4)
  have h2 := fourth_power_centered_bound a ((1 - p) * b / 4)
  have h3 := mul_le_mul_of_nonneg_left h1 hq
  have h4 := mul_le_mul_of_nonneg_left h2 hp
  have hvar : 0 ≤ p * (1 - p) := mul_nonneg hp hq
  have hvar1 : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hpq : (1 - p) ^ 3 + p ^ 3 ≤ 1 := by nlinarith
  have hab : 0 ≤ a ^ 2 * b ^ 2 := mul_nonneg (sq_nonneg a) (sq_nonneg b)
  have hb4 : 0 ≤ b ^ 4 := by positivity
  have hvarab := mul_le_mul_of_nonneg_right hvar1 hab
  have hfour := mul_le_mul_of_nonneg_left hpq hvar
  have hfourb := mul_le_mul_of_nonneg_right hfour hb4
  have hvarb := mul_le_mul_of_nonneg_right hvar1 hb4
  nlinarith only [h3, h4, hvarab, hfourb, hvarb, hab, hb4]

/-- Mean and variance decomposition for a two-point law, without division. -/
lemma two_point_second_moment (p u v : ℝ) :
    ((1 - p) * u + p * v) ^ 2 + p * (1 - p) * (v - u) ^ 2 =
      (1 - p) * u ^ 2 + p * v ^ 2 := by
  ring

/-- The scalar noise contraction in raw function values. This is the
`(1 - ρ) * expectation + ρ * identity` form, suitable for tensor products. -/
theorem biased_two_point_noise_fourth (p ρ u v : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hρ : 16 * ρ ^ 2 ≤ p * (1 - p)) :
    let μ := (1 - p) * u + p * v
    (1 - p) * (μ + ρ * (u - μ)) ^ 4 + p * (μ + ρ * (v - μ)) ^ 4 ≤
      ((1 - p) * u ^ 2 + p * v ^ 2) ^ 2 := by
  dsimp only
  have h := biased_two_point_fourth_moment p ((1 - p) * u + p * v)
    (4 * ρ * (v - u)) hp hp1
  have hleft : (1 - p) * u + p * v - p * (4 * ρ * (v - u)) / 4 =
      (1 - p) * u + p * v + ρ * (u - ((1 - p) * u + p * v)) := by ring
  have hright : (1 - p) * u + p * v + (1 - p) * (4 * ρ * (v - u)) / 4 =
      (1 - p) * u + p * v + ρ * (v - ((1 - p) * u + p * v)) := by ring
  rw [hleft, hright] at h
  refine h.trans ?_
  have hc := mul_le_mul_of_nonneg_right hρ (sq_nonneg (v - u))
  have hm := two_point_second_moment p u v
  have hbound : ((1 - p) * u + p * v) ^ 2 + (4 * ρ * (v - u)) ^ 2 ≤
      (1 - p) * u ^ 2 + p * v ^ 2 := by nlinarith only [hc, hm]
  exact pow_le_pow_left₀ (by positivity) hbound 2

/-- Finite-sum formulation of the two-point noise contraction. -/
theorem biased_bool_noise_fourth (p ρ : ℝ) (f : Bool → ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hρ : 16 * ρ ^ 2 ≤ p * (1 - p)) :
    let w : Bool → ℝ := fun b => if b = true then p else 1 - p
    let μ := ∑ b, w b * f b
    ∑ b, w b * ((1 - ρ) * μ + ρ * f b) ^ 4 ≤
      (∑ b, w b * (f b) ^ 2) ^ 2 := by
  dsimp only
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
  have h := biased_two_point_noise_fourth p ρ (f false) (f true) hp hp1 hρ
  dsimp only at h
  convert h using 1 <;> ring

end Problem313

end

end OAI
