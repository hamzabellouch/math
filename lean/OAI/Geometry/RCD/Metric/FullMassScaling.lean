import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! # Uniform scaling of the full Bochner mass estimate -/

namespace RegularPointCoordinates

/-- The cutoff factor times radius squared has the expected volume scale. -/
theorem scaled_cutoff_mass_factor {s c k v V : ℝ} {n : ℕ}
    (hs : 0 < s) (hc : 0 ≤ c) (hk : 0 ≤ k) (hV : 0 ≤ V)
    (hcurv : k * s ^ 2 ≤ 1) (hvol : v ≤ V * s ^ n) :
    ((((c / (3 * (s / 49152)) ^ 2) / 2 + k) * v) * s ^ 2) ≤
      (c * (49152 : ℝ) ^ 2 / 18 + 1) * V * s ^ n := by
  have heq : (((c / (3 * (s / 49152)) ^ 2) / 2 + k) * v) * s ^ 2 =
      (c * (49152 : ℝ) ^ 2 / 18 + k * s ^ 2) * v := by
    field_simp [hs.ne']; ring
  rw [heq]
  calc
    _ ≤ (c * (49152 : ℝ) ^ 2 / 18 + k * s ^ 2) * (V * s ^ n) := by gcongr
    _ ≤ (c * (49152 : ℝ) ^ 2 / 18 + 1) * (V * s ^ n) := by gcongr
    _ = _ := by ring

/-- Combining the actual source budget and scaled cutoff estimate leaves
one uniform constant times radius to the dimension times source squared. -/
theorem full_mass_scaling {s P F Cs Cf R Q L sigma : ℝ} {n : ℕ}
    (_hs : 0 ≤ s) (_hCs : 0 ≤ Cs) (_hCf : 0 ≤ Cf) (hR : 0 ≤ R)
    (hP : P ≤ 2 * Cs * s ^ n * sigma ^ 2)
    (hF : F * s ^ 2 ≤ Cf * s ^ n) :
    4 * (P + F * (Q ^ 2 * s ^ 2 * sigma ^ 2)) +
      4 * (F * (16 * (n : ℝ) ^ 2)) *
        ((2 * Real.sqrt R * (L * s * sigma)) ^ 2 + Q ^ 2 * s ^ 2 * sigma ^ 2) ≤
      (8 * Cs + 4 * Cf * (Q ^ 2 + 16 * (n : ℝ) ^ 2 * (4 * R * L ^ 2 + Q ^ 2))) *
        s ^ n * sigma ^ 2 := by
  have heq : 4 * (P + F * (Q ^ 2 * s ^ 2 * sigma ^ 2)) +
      4 * (F * (16 * (n : ℝ) ^ 2)) *
        ((2 * Real.sqrt R * (L * s * sigma)) ^ 2 + Q ^ 2 * s ^ 2 * sigma ^ 2) =
      4 * P + 4 * (F * s ^ 2) * (Q ^ 2 + 16 * (n : ℝ) ^ 2 * (4 * R * L ^ 2 + Q ^ 2)) * sigma ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt hR]
    ring
  rw [heq]
  calc
    _ ≤ 4 * (2 * Cs * s ^ n * sigma ^ 2) +
        4 * (Cf * s ^ n) * (Q ^ 2 + 16 * (n : ℝ) ^ 2 * (4 * R * L ^ 2 + Q ^ 2)) * sigma ^ 2 := by
      gcongr
    _ = _ := by ring

end RegularPointCoordinates

end OAI
