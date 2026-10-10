import Mathlib

namespace OAI
noncomputable section
namespace Problem337

lemma two_mul_le_sin_pi_mul {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1/2) :
    2*x ≤ Real.sin (Real.pi*x) := by
  have h := Real.mul_le_sin (x := Real.pi*x) (by positivity) (by nlinarith [Real.pi_pos])
  have he : (2 / Real.pi) * (Real.pi*x) = 2*x := by field_simp
  rwa [he] at h

/-- Sine is uniformly bounded below away from both endpoints of the unit interval. -/
theorem sin_pi_mul_lower_of_margin {a x : ℝ} (ha : 0 ≤ a)
    (hlo : a ≤ x) (hhi : x ≤ 1-a) : 2*a ≤ Real.sin (Real.pi*x) := by
  by_cases hx : x ≤ 1/2
  · exact (by linarith : 2*a ≤ 2*x).trans (two_mul_le_sin_pi_mul (by linarith) hx)
  · have h := two_mul_le_sin_pi_mul (x := 1-x) (by linarith) (by linarith)
    have he : Real.sin (Real.pi*(1-x)) = Real.sin (Real.pi*x) := by
      rw [mul_sub, mul_one, Real.sin_pi_sub]
    rw [he] at h
    linarith

/-- The inner interval stays separated, in both cyclic directions, from its complement. -/
theorem inner_interval_difference_margin {δ a t x : ℝ} (_ha : 0 ≤ a)
    (htlo : a ≤ t) (hthi : t ≤ δ-a) (hxlo : δ ≤ x) (hxhi : x ≤ 1) :
    a ≤ x-t ∧ x-t ≤ 1-a := by
  constructor <;> linarith

/-- A geometric-sum denominator for an inner-interval kernel is bounded away from zero
at every point outside the target interval. -/
theorem inner_interval_sine_lower {δ a t x : ℝ} (ha : 0 ≤ a)
    (htlo : a ≤ t) (hthi : t ≤ δ-a) (hxlo : δ ≤ x) (hxhi : x ≤ 1) :
    2*a ≤ Real.sin (Real.pi*(x-t)) := by
  obtain ⟨hlo,hhi⟩ := inner_interval_difference_margin ha htlo hthi hxlo hxhi
  exact sin_pi_mul_lower_of_margin ha hlo hhi

/-- Squaring the reciprocal sine bound gives the standard pointwise Fejer leakage. -/
theorem inner_interval_inverse_sin_sq {δ a t x h : ℝ} (ha : 0 < a) (hh : 0 < h)
    (htlo : a ≤ t) (hthi : t ≤ δ-a) (hxlo : δ ≤ x) (hxhi : x ≤ 1) :
    1/(h*(Real.sin (Real.pi*(x-t)))^2) ≤ 1/(4*h*a^2) := by
  have hs := inner_interval_sine_lower ha.le htlo hthi hxlo hxhi
  have hspos : 0 < Real.sin (Real.pi*(x-t)) := by linarith
  apply one_div_le_one_div_of_le (by positivity)
  have hs2 : (2*a)^2 ≤ (Real.sin (Real.pi*(x-t)))^2 :=
    pow_le_pow_left₀ (by positivity) hs 2
  nlinarith [mul_le_mul_of_nonneg_left hs2 hh.le]

/-- Natural lattice points in a half-open normalized interval. -/
def innerGridInterval (q : ℕ) (a b : ℝ) : Finset ℕ :=
  Finset.Ico (Nat.ceil (a*q)) (Nat.ceil (b*q))

lemma innerGridInterval_mem {q j : ℕ} (hq : 0 < q) {a b : ℝ}
    (hb : b ≤ 1) (hj : j ∈ innerGridInterval q a b) :
    j < q ∧ a ≤ (j : ℝ)/q ∧ (j : ℝ)/q < b := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hj
  have hloR : a*q ≤ (j : ℝ) := Nat.ceil_le.mp hlo
  have hhiR : (j : ℝ) < b*q := Nat.lt_ceil.mp hhi
  refine ⟨?_, (le_div_iff₀ hqR).mpr hloR, (div_lt_iff₀ hqR).mpr hhiR⟩
  have : (j : ℝ) < q := lt_of_lt_of_le hhiR (by nlinarith)
  exact_mod_cast this

/-- Rounding loses at most one lattice point from the expected interval length. -/
theorem innerGridInterval_card_bounds (q : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (b-a)*(q : ℝ)-1 ≤ ((innerGridInterval q a b).card : ℝ) ∧
      ((innerGridInterval q a b).card : ℝ) ≤ (b-a)*(q : ℝ)+1 := by
  have haq : 0 ≤ a*(q : ℝ) := by positivity
  have hb : 0 ≤ b := ha.trans hab
  have hbq : 0 ≤ b*(q : ℝ) := by positivity
  have hle : Nat.ceil (a*(q : ℝ)) ≤ Nat.ceil (b*(q : ℝ)) :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_right hab (by positivity))
  have hcard : ((innerGridInterval q a b).card : ℝ) =
      (Nat.ceil (b*(q : ℝ)) : ℝ) - (Nat.ceil (a*(q : ℝ)) : ℝ) := by
    simp only [innerGridInterval, Nat.card_Ico]
    exact Nat.cast_sub hle
  rw [hcard]
  have hal := Nat.le_ceil (a*(q : ℝ))
  have hau := Nat.ceil_lt_add_one haq
  have hbl := Nat.le_ceil (b*(q : ℝ))
  have hbu := Nat.ceil_lt_add_one hbq
  constructor <;> nlinarith

/-- The standard inner three-quarter interval has cardinality close to `3δq/4`. -/
theorem innerGridInterval_three_quarters (q : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    3*δ*(q : ℝ)/4-1 ≤ ((innerGridInterval q (δ/8) (7*δ/8)).card : ℝ) ∧
      ((innerGridInterval q (δ/8) (7*δ/8)).card : ℝ) ≤ 3*δ*(q : ℝ)/4+1 := by
  have h := innerGridInterval_card_bounds q (a := δ/8) (b := 7*δ/8)
    (by positivity) (by linarith)
  constructor <;> nlinarith [h.1, h.2]

end Problem337

end

end OAI
