import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGridApproximation

namespace OAI

/-! # A polynomial grid-error bound on the manuscript's parameter box -/

namespace Ostmann

open scoped SchwartzMap

theorem quadraticGridError_le_power (X : ℝ) (q s : ℕ) (B Rmax v H : ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (hX : 2 ≤ X) (hpi : 2 * Real.pi ≤ X)
    (hq1 : 1 ≤ q) (hq : (q : ℝ) ≤ X) (hs1 : 1 ≤ s) (hs : (s : ℝ) ≤ X ^ 28)
    (hv1 : 1 ≤ v) (hv : v ≤ X) (hB0 : 0 ≤ B) (hB : B ≤ X)
    (hR0 : 0 ≤ Rmax) (hR : Rmax ≤ X ^ 14) (hH0 : 0 ≤ H) (hH : H ≤ X)
    (hΦ0 : SchwartzMap.seminorm ℝ 0 0 Φ ≤ X)
    (hΦ1 : SchwartzMap.seminorm ℝ 0 1 Φ ≤ X) :
    quadraticGridError q s B Rmax v H Φ ≤ X ^ 72 := by
  have hX0 : 0 ≤ X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hs1' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hv0 : 0 ≤ v := by linarith
  have hsv : 1 ≤ (s : ℝ) * v := one_le_mul_of_one_le_of_one_le hs1' hv1
  have ha : (s : ℝ) * v / q ≤ X ^ 29 := by
    calc
      _ ≤ (s : ℝ) * v := div_le_self (by positivity) hq1'
      _ ≤ X ^ 28 * X := mul_le_mul hs hv hv0 (by positivity)
      _ = X ^ 29 := by ring
  have harg : H * Rmax * q / ((s : ℝ) * v) ≤ (X ^ 8) ^ 2 := by
    calc
      _ ≤ H * Rmax * q := div_le_self (by positivity) hsv
      _ ≤ X * X ^ 14 * X := by gcongr
      _ = _ := by ring
  let W := ⌊Real.sqrt (H * Rmax * q / ((s : ℝ) * v))⌋₊
  have hW : (W : ℝ) ≤ X ^ 8 := by
    apply (Nat.floor_le (Real.sqrt_nonneg _)).trans
    apply (Real.sqrt_le_sqrt harg).trans_eq
    exact Real.sqrt_sq (pow_nonneg hX0 _)
  have hD : Real.sqrt ((s : ℝ) * v / q) ≤ X ^ 15 := by
    have hh : X ^ 29 ≤ (X ^ 15) ^ 2 := by
      calc
        _ ≤ X ^ 30 := pow_le_pow_right₀ hX1 (by omega)
        _ = _ := by ring
    exact (Real.sqrt_le_sqrt (ha.trans hh)).trans_eq (Real.sqrt_sq (pow_nonneg hX0 _))
  have hsqrtH : Real.sqrt H ≤ X := by
    have hh : X ≤ X ^ 2 := by nlinarith
    exact (Real.sqrt_le_sqrt (hH.trans hh)).trans_eq (Real.sqrt_sq hX0)
  have htheta : B * SchwartzMap.seminorm ℝ 0 0 Φ * (2 * Real.pi * H * Rmax) * Real.sqrt H ≤ X ^ 19 := by
    calc
      _ ≤ X * X * (X * X * X ^ 14) * X := by gcongr
      _ = _ := by ring
  have hscale : Real.sqrt ((s : ℝ) * v / q) * W * B *
      (SchwartzMap.seminorm ℝ 0 0 Φ +
        SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2) ≤ X ^ 25 + X ^ 70 := by
    calc
      _ ≤ X ^ 15 * X ^ 8 * X * (X + X * X ^ 29 * (X ^ 8) ^ 2) := by gcongr
      _ = _ := by ring
  unfold quadraticGridError
  change _ + (_ * (W : ℝ) * _ * _) ≤ _
  calc
    _ ≤ X ^ 19 + (X ^ 25 + X ^ 70) := add_le_add htheta hscale
    _ ≤ 3 * X ^ 70 := by
      have ha := pow_le_pow_right₀ hX1 (show 19 ≤ 70 by omega)
      have hb := pow_le_pow_right₀ hX1 (show 25 ≤ 70 by omega)
      linarith
    _ ≤ X ^ 2 * X ^ 70 := by gcongr; nlinarith
    _ = _ := by ring

end Ostmann

end OAI
