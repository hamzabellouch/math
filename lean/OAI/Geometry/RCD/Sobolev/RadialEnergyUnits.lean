import OAI.Geometry.RCD.Harmonic.RadialErrorUnits

namespace OAI

/-! # Scale-independent constants for the radial fit energy -/

noncomputable section
namespace RegularPointCoordinates

def radialEnergyConstant (K : ℝ) (n : ℕ) (G ε A B J Cχ : ℝ) : ℝ :=
  1 + 8 * G ^ 2 +
    (8 + 16 * G ^ 2 * annularPoincareConstant K n) *
      (((n + 2 : ℕ) : ℝ) * (1 + ε + A)) ^ 2 * (4096 * Cχ * (J + B / 2) + A ^ 2) +
    32768 * G ^ 2 * ((n : ℝ) * (1 + ε)) ^ 2 * B

theorem radialEnergyConstant_pos {K G ε A B J Cχ : ℝ} {n : ℕ}
    (hB : 0 ≤ B) (hJ : 0 ≤ J) (hCχ : 0 ≤ Cχ) :
    0 < radialEnergyConstant K n G ε A B J Cχ := by
  have hp := (annularPoincareConstant_pos K n).le
  dsimp only [radialEnergyConstant]
  positivity

/-- The testing radius s/64 and its Poincare constant cancel all length
units in the weak-radial interior estimate. -/
theorem radial_energy_natural_units {K G ε A B J Cχ s κ σ V L I b t : ℝ} {n : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hκ : 0 ≤ κ) (hσ : 0 ≤ σ) (hV : 0 ≤ V)
    (hB : 0 ≤ B) (hJ : 0 ≤ J) (hA : 0 ≤ A) (hε : 0 ≤ ε) (hCχ : 0 ≤ Cχ) (hI : 0 ≤ I)
    (hL : L = ((n + 2 : ℕ) : ℝ) * max (1 + ε) (A * s))
    (ht : t ≤ 8 * (L ^ 2 * b ^ 2 * (4096 * Cχ * (J + B / 2) * σ + κ * A ^ 2 * s ^ 2 * V)) +
      4 * (G / (s / 64)) ^ 2 *
        (2 * I + 2 * (((n : ℝ) * (1 + ε)) ^ 2 * b ^ 2) * (σ * (B * s ^ 2)) +
          4 * (annularPoincareConstant K n * (s / 64) ^ 2) *
            (L ^ 2 * b ^ 2 * (4096 * Cχ * (J + B / 2) * σ + κ * A ^ 2 * s ^ 2 * V)))) :
    t ≤ radialEnergyConstant K n G ε A B J Cχ *
      (I / (s / 64) ^ 2 + (σ + κ * s ^ 2 * V) * b ^ 2) := by
  let N := ((n + 2 : ℕ) : ℝ) * (1 + ε + A)
  let H := 4096 * Cχ * (J + B / 2) + A ^ 2
  let Y := σ + κ * s ^ 2 * V
  let P := annularPoincareConstant K n
  let Q := (8 + 16 * G ^ 2 * P) * N ^ 2 * H +
    32768 * G ^ 2 * ((n : ℝ) * (1 + ε)) ^ 2 * B
  have hP : 0 ≤ P := (annularPoincareConstant_pos K n).le
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hLN : L ≤ N := by
    rw [hL]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply max_le
    · exact le_add_of_nonneg_right hA
    · have hh := mul_le_mul_of_nonneg_left hs1 hA
      have hh' : A * s ≤ A := by simpa only [mul_one] using hh
      exact hh'.trans (le_add_of_nonneg_left (add_nonneg zero_le_one hε))
  have hLs : L ^ 2 ≤ N ^ 2 := (sq_le_sq₀ hL0 hN).mpr hLN
  have hmass : 4096 * Cχ * (J + B / 2) * σ + κ * A ^ 2 * s ^ 2 * V ≤ H * Y := by
    dsimp only [H, Y]
    nlinarith only [mul_nonneg (sq_nonneg A) hσ,
      mul_nonneg (by positivity : 0 ≤ 4096 * Cχ * (J + B / 2))
        (by positivity : 0 ≤ κ * s ^ 2 * V)]
  have hess : L ^ 2 * b ^ 2 * (4096 * Cχ * (J + B / 2) * σ + κ * A ^ 2 * s ^ 2 * V) ≤
      N ^ 2 * H * Y * b ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hmass (mul_nonneg (sq_nonneg L) (sq_nonneg b))
    have hl := mul_le_mul_of_nonneg_right hLs (mul_nonneg (sq_nonneg b) (mul_nonneg hH hY))
    apply hm.trans
    convert hl using 1 <;> ring
  have hσY : σ ≤ Y := le_add_of_nonneg_right (by positivity)
  have hformula : 8 * (L ^ 2 * b ^ 2 * (4096 * Cχ * (J + B / 2) * σ + κ * A ^ 2 * s ^ 2 * V)) +
      4 * (G / (s / 64)) ^ 2 *
        (2 * I + 2 * (((n : ℝ) * (1 + ε)) ^ 2 * b ^ 2) * (σ * (B * s ^ 2)) +
          4 * (P * (s / 64) ^ 2) *
            (L ^ 2 * b ^ 2 * (4096 * Cχ * (J + B / 2) * σ + κ * A ^ 2 * s ^ 2 * V))) =
      8 * G ^ 2 * (I / (s / 64) ^ 2) +
      (8 + 16 * G ^ 2 * P) *
        (L ^ 2 * b ^ 2 * (4096 * Cχ * (J + B / 2) * σ + κ * A ^ 2 * s ^ 2 * V)) +
      32768 * G ^ 2 * ((n : ℝ) * (1 + ε)) ^ 2 * B * σ * b ^ 2 := by
    generalize hz : L ^ 2 * b ^ 2 *
      (4096 * Cχ * (J + B / 2) * σ + κ * A ^ 2 * s ^ 2 * V) = z
    generalize hu : ((n : ℝ) * (1 + ε)) ^ 2 = u
    field_simp [hs.ne']
    ring
  rw [hformula] at ht
  have hh := mul_le_mul_of_nonneg_left hess
    (show 0 ≤ 8 + 16 * G ^ 2 * P by positivity)
  have hsource := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hσY
      (show 0 ≤ 32768 * G ^ 2 * ((n : ℝ) * (1 + ε)) ^ 2 * B by positivity)) (sq_nonneg b)
  have hmain : t ≤ 8 * G ^ 2 * (I / (s / 64) ^ 2) + Q * (Y * b ^ 2) := by
    apply ht.trans
    calc
      _ ≤ 8 * G ^ 2 * (I / (s / 64) ^ 2) +
          (8 + 16 * G ^ 2 * P) * (N ^ 2 * H * Y * b ^ 2) +
          32768 * G ^ 2 * ((n : ℝ) * (1 + ε)) ^ 2 * B * Y * b ^ 2 :=
        add_le_add (add_le_add_right hh _) hsource
      _ = _ := by dsimp only [Q]; ring
  have hD : radialEnergyConstant K n G ε A B J Cχ = 1 + 8 * G ^ 2 + Q := by
    dsimp only [radialEnergyConstant, Q]
    exact add_assoc _ _ _
  have hfirst := mul_le_mul_of_nonneg_right
    (show 8 * G ^ 2 ≤ radialEnergyConstant K n G ε A B J Cχ by
      rw [hD]
      exact (le_add_of_nonneg_left zero_le_one).trans (le_add_of_nonneg_right hQ))
    (div_nonneg hI (sq_nonneg (s / 64)))
  have hsecond := mul_le_mul_of_nonneg_right
    (show Q ≤ radialEnergyConstant K n G ε A B J Cχ by
      rw [hD]
      exact le_add_of_nonneg_left (add_nonneg zero_le_one (mul_nonneg (by norm_num) (sq_nonneg G))))
    (mul_nonneg hY (sq_nonneg b))
  exact hmain.trans ((add_le_add hfirst hsecond).trans_eq (by ring))

end RegularPointCoordinates

end

end OAI
