import OAI.NumberTheory.EgyptianFractions.ForwardDifference
import OAI.NumberTheory.EgyptianFractions.ReciprocalPhaseScale

namespace OAI
noncomputable section

namespace Problem337

/-- The exact scale normalization used in the second derivative test. -/
theorem reciprocal_second_derivative_comparison (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) (Z : ℝ) {U x : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hxend : x + hs.sum ≤ 2 * U) :
    let k := hs.length + 2
    let Λ := |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod
    (k.factorial : ℝ) / (2 : ℝ) ^ (k + 1) * Λ ≤
      |iteratedDeriv 2 (forwardDifference hs (fun y => Z / y)) x| ∧
    |iteratedDeriv 2 (forwardDifference hs (fun y => Z / y)) x| ≤
      (k.factorial : ℝ) * Λ := by
  dsimp only
  have hpow : U ^ (-(((hs.length + 2 : ℕ) : ℝ) + 1)) = 1 / U ^ (hs.length + 2 + 1) := by
    rw [Real.rpow_neg hU.le]
    norm_cast
    simp only [one_div]
  rw [hpow]
  obtain ⟨hl, hu⟩ := reciprocal_forwardDifference_derivative_bounds 2 hs hhs Z hU hx hxend
  constructor
  · convert hl using 1
    rw [mul_pow]
    ring
  · convert hu using 1
    ring

/-- Scalar terminal estimate for a second-derivative bound. -/
theorem reciprocal_terminal_error_bound {U a b Λ : ℝ} (hU : 1 ≤ U)
    (ha : 0 < a) (hb : 0 ≤ b)
    (hlower : a * U ^ (-(3 : ℝ) / 2) ≤ Λ)
    (hupper : Λ ≤ b * U ^ (-(2 : ℝ) / 5)) :
    U * Λ ^ ((1 : ℝ) / 2) + Λ ^ (-(1 : ℝ) / 2) + 1 ≤
      (b ^ ((1 : ℝ) / 2) + a ^ (-(1 : ℝ) / 2) + 1) * U ^ ((4 : ℝ) / 5) := by
  have hU0 : 0 < U := by linarith
  have hΛ : 0 < Λ := (mul_pos ha (Real.rpow_pos_of_pos hU0 _)).trans_le hlower
  have hroot := Real.rpow_le_rpow hΛ.le hupper (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [Real.mul_rpow hb (by positivity), ← Real.rpow_mul hU0.le] at hroot
  norm_num at hroot
  have hfirst : U * Λ ^ ((1 : ℝ) / 2) ≤ b ^ ((1 : ℝ) / 2) * U ^ ((4 : ℝ) / 5) := by
    calc
      U * Λ ^ ((1 : ℝ) / 2) ≤ U * (b ^ ((1 : ℝ) / 2) * U ^ (-(1 : ℝ) / 5)) :=
        mul_le_mul_of_nonneg_left (by simpa only [neg_div] using hroot) hU0.le
      _ = b ^ ((1 : ℝ) / 2) * U ^ ((4 : ℝ) / 5) := by
        rw [mul_left_comm]
        congr 1
        calc
          U * U ^ (-(1 : ℝ) / 5) = U ^ (1 : ℝ) * U ^ (-(1 : ℝ) / 5) := by rw [Real.rpow_one]
          _ = U ^ ((1 : ℝ) + -(1 : ℝ) / 5) := (Real.rpow_add hU0 _ _).symm
          _ = U ^ ((4 : ℝ) / 5) := by norm_num
  have hinv := Real.rpow_le_rpow_of_nonpos
    (mul_pos ha (Real.rpow_pos_of_pos hU0 _)) hlower
    (by norm_num : (-(1 : ℝ) / 2) ≤ 0)
  rw [Real.mul_rpow ha.le (by positivity), ← Real.rpow_mul hU0.le] at hinv
  norm_num at hinv
  have hsecond : Λ ^ (-(1 : ℝ) / 2) ≤ a ^ (-(1 : ℝ) / 2) * U ^ ((4 : ℝ) / 5) := by
    simpa only [neg_div] using hinv.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU (by norm_num : (3 : ℝ) / 4 ≤ 4 / 5)) (by positivity))
  have hone : 1 ≤ U ^ ((4 : ℝ) / 5) := Real.one_le_rpow hU (by norm_num)
  nlinarith

/-- Flexible range factor in the normalized second-derivative comparison.
Taking `C=3` or `C=4` accommodates endpoint samples without dropping terms. -/
theorem reciprocal_second_derivative_comparison_general (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) (Z C : ℝ) {U x : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hxend : x + hs.sum ≤ C * U) :
    let k := hs.length + 2
    let Λ := |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod
    (k.factorial : ℝ) / C ^ (k + 1) * Λ ≤
      |iteratedDeriv 2 (forwardDifference hs (fun y => Z / y)) x| ∧
    |iteratedDeriv 2 (forwardDifference hs (fun y => Z / y)) x| ≤
      (k.factorial : ℝ) * Λ := by
  dsimp only
  have hpow : U ^ (-(((hs.length + 2 : ℕ) : ℝ) + 1)) = 1 / U ^ (hs.length + 2 + 1) := by
    rw [Real.rpow_neg hU.le]
    norm_cast
    simp only [one_div]
  rw [hpow]
  obtain ⟨hl, hu⟩ := reciprocal_forwardDifference_derivative_bounds_interval 2 hs hhs Z hU hx hxend
  constructor
  · convert hl using 1
    rw [mul_pow]
    ring
  · convert hu using 1
    ring

end Problem337

end

end OAI
