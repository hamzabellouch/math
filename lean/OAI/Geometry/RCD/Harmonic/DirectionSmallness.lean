import OAI.Geometry.RCD.Harmonic.DirectionRecoveryScale

namespace OAI

/-! # One scale-independent tolerance for actual direction recovery -/

namespace RegularPointCoordinates

/-- A single tolerance controls the two Gram restrictions, the radial
matrix error, and the absorption term at every positive physical radius. -/
theorem direction_smallness_parameters (n : ℕ) (Ca D Q V G : ℝ)
    (hQ : 0 ≤ Q) (hV : 0 ≤ V) (hG : 0 ≤ G) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * (2 : ℝ) ^ n) * tau) ≤ 1 / 3 ∧
      (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * (8192 : ℝ) ^ n) * tau) ≤ 1 / 2 ∧
      ∀ z E : ℝ, 0 ≤ z → z ≤ tau → 0 ≤ E → E ≤ tau →
        2 * ((n : ℝ) ^ 4 * Real.sqrt (2 * Ca ^ 2 * (D ^ 2 * E + Q * z))) ≤ 1 / 4 ∧
        ∀ s : ℝ, 0 < s →
          (4 * (G / (s / 2048))) * Real.sqrt (V * s ^ 2 * E) ≤ 1 / 2 := by
  let L1 := (n : ℝ) ^ 2 * ((5 / 3 : ℝ) * (2 : ℝ) ^ n)
  let L2 := (n : ℝ) ^ 2 * ((5 / 3 : ℝ) * (8192 : ℝ) ^ n)
  let a := 2 * (n : ℝ) ^ 4 * Real.sqrt (2 * Ca ^ 2 * (D ^ 2 + Q))
  let b := 8192 * G * Real.sqrt V
  have hL1 : 0 ≤ L1 := by dsimp only [L1]; positivity
  have hL2 : 0 ≤ L2 := by dsimp only [L2]; positivity
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  let t := 1 / (4 * (a + b + 1))
  have ht : 0 < t := by dsimp only [t]; positivity
  have hteq : (a + b + 1) * t = 1 / 4 := by
    dsimp only [t]
    field_simp
  let tau := min (1 / (3 * (L1 + 1))) (min (1 / (2 * (L2 + 1))) (min 1 (t ^ 2)))
  have htau : 0 < tau := by dsimp only [tau]; positivity
  have hbounds : tau ≤ 1 / (3 * (L1 + 1)) ∧ tau ≤ 1 / (2 * (L2 + 1)) ∧
      tau ≤ 1 ∧ tau ≤ t ^ 2 := by
    have h : tau ≤ tau := le_rfl
    simpa only [tau, le_min_iff] using h
  have h1 := (le_div_iff₀ (by positivity : 0 < 3 * (L1 + 1))).mp hbounds.1
  have h2 := (le_div_iff₀ (by positivity : 0 < 2 * (L2 + 1))).mp hbounds.2.1
  have hroot : Real.sqrt tau ≤ t := by
    have hh := Real.sqrt_le_sqrt hbounds.2.2.2
    simpa only [Real.sqrt_sq ht.le] using hh
  refine ⟨tau, htau, hbounds.2.2.1, ?_, ?_, ?_⟩
  · have hh : L1 * tau ≤ 1 / 3 := by nlinarith only [h1, htau.le]
    simpa only [L1, mul_assoc] using hh
  · have hh : L2 * tau ≤ 1 / 2 := by nlinarith only [h2, htau.le]
    simpa only [L2, mul_assoc] using hh
  · intro z E hz hzt hE hEt
    have hsum : D ^ 2 * E + Q * z ≤ (D ^ 2 + Q) * tau := by
      nlinarith only [mul_le_mul_of_nonneg_left hEt (sq_nonneg D),
        mul_le_mul_of_nonneg_left hzt hQ]
    have hmatrix := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * Ca ^ 2))
    rw [show 2 * Ca ^ 2 * ((D ^ 2 + Q) * tau) = (2 * Ca ^ 2 * (D ^ 2 + Q)) * tau by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 2 * Ca ^ 2 * (D ^ 2 + Q))] at hmatrix
    have hmatrix' := mul_le_mul_of_nonneg_left hmatrix (by positivity : 0 ≤ 2 * (n : ℝ) ^ 4)
    have haroot := mul_le_mul_of_nonneg_left hroot ha
    have hat : a * t ≤ 1 / 4 := by
      nlinarith only [hteq, mul_nonneg hb ht.le, ht.le]
    refine ⟨?_, ?_⟩
    · calc
        _ ≤ a * Real.sqrt tau := by simpa only [a, mul_assoc] using hmatrix'
        _ ≤ a * t := haroot
        _ ≤ 1 / 4 := hat
    · intro s hs
      have hEroot := Real.sqrt_le_sqrt hEt
      have hbt : b * t ≤ 1 / 4 := by
        nlinarith only [hteq, mul_nonneg ha ht.le, ht.le]
      have hbe : b * Real.sqrt E ≤ 1 / 4 :=
        (mul_le_mul_of_nonneg_left (hEroot.trans hroot) hb).trans hbt
      have heq : (4 * (G / (s / 2048))) * Real.sqrt (V * s ^ 2 * E) = b * Real.sqrt E := by
        rw [show V * s ^ 2 * E = s ^ 2 * (V * E) by ring,
          Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le, Real.sqrt_mul hV]
        dsimp only [b]
        field_simp; ring
      rw [heq]
      linarith only [hbe]

end RegularPointCoordinates

end OAI
