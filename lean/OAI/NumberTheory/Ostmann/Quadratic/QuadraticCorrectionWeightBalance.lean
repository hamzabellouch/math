import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionCutoffGeometry

namespace OAI

/-! # The actual cutoff geometry balances the low and high divisor weights -/

namespace Ostmann

theorem quadratic_correction_weight_identity {M H : ℝ} {e B : ℕ}
    (hM : 0 < M) (hH : 0 < H) (he : 0 < e) (hB : 0 < B) :
    (M / ((e : ℝ) * H)) * quadraticCorrectionBase M H e B =
      Real.sqrt M / (Real.sqrt e * Real.sqrt B) := by
  rw [quadratic_correction_base_formula hM hH he hB]
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hsM := Real.sq_sqrt hM.le
  have hse := Real.sq_sqrt heR.le
  have hsM₀ := (Real.sqrt_pos.mpr hM).ne'
  have hse₀ := (Real.sqrt_pos.mpr heR).ne'
  have hsB₀ := (Real.sqrt_pos.mpr (show (0 : ℝ) < B by exact_mod_cast hB)).ne'
  field_simp
  nlinarith

theorem quadratic_low_weight_balance {M H J : ℝ} {e B D : ℕ}
    (hM : 0 < M) (hH : 0 < H) (he : 0 < e) (hB : 0 < B) (hD : 0 < D)
    (hJ : 1 ≤ J) (hcut : (D : ℝ) ≤ 2 * quadraticCorrectionBase M H e B * J) :
    M / ((e : ℝ) * H) ≤
      2 * J * min (M / ((e : ℝ) * H))
        (Real.sqrt M / (Real.sqrt e * Real.sqrt B * D)) := by
  let α := M / ((e : ℝ) * H)
  let β := Real.sqrt M / (Real.sqrt e * Real.sqrt B)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hi : α * quadraticCorrectionBase M H e B = β :=
    quadratic_correction_weight_identity hM hH he hB
  have hh := mul_le_mul_of_nonneg_left hcut hα
  have hab : α ≤ 2 * J * (β / D) := by
    calc
      α ≤ (2 * J * β) / D := (le_div_iff₀ hDR).mpr (by nlinarith [hi])
      _ = _ := by ring
  have hαJ : α ≤ 2 * J * α := by nlinarith
  change α ≤ 2 * J * min α (Real.sqrt M / (Real.sqrt e * Real.sqrt B * D))
  have heq : Real.sqrt M / (Real.sqrt e * Real.sqrt B * D) = β / D := by dsimp [β]; ring
  rw [heq]
  by_cases hle : α ≤ β / D
  · rw [min_eq_left hle]
    exact hαJ
  · rw [min_eq_right (le_of_not_ge hle)]
    exact hab

theorem quadratic_high_weight_balance {M H J : ℝ} {e B D : ℕ}
    (hM : 0 < M) (hH : 0 < H) (he : 0 < e) (hB : 0 < B) (hD : 0 < D)
    (hJ : 1 ≤ J) (hcut : quadraticCorrectionBase M H e B / (8 * J) ≤ (D : ℝ)) :
    Real.sqrt M / (Real.sqrt e * Real.sqrt B * D) ≤
      8 * J * min (M / ((e : ℝ) * H))
        (Real.sqrt M / (Real.sqrt e * Real.sqrt B * D)) := by
  let α := M / ((e : ℝ) * H)
  let β := Real.sqrt M / (Real.sqrt e * Real.sqrt B)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hJpos : 0 < 8 * J := by positivity
  have hi : α * quadraticCorrectionBase M H e B = β :=
    quadratic_correction_weight_identity hM hH he hB
  have hcut' : quadraticCorrectionBase M H e B ≤ (D : ℝ) * (8 * J) :=
    (div_le_iff₀ hJpos).mp hcut
  have hh := mul_le_mul_of_nonneg_left hcut' hα
  have hab : β / D ≤ 8 * J * α := by
    apply (div_le_iff₀ hDR).mpr
    nlinarith [hi]
  have hβJ : β / D ≤ 8 * J * (β / D) := by
    have hn : 0 ≤ β / D := div_nonneg hβ hDR.le
    nlinarith
  have heq : Real.sqrt M / (Real.sqrt e * Real.sqrt B * D) = β / D := by dsimp [β]; ring
  rw [heq]
  change β / D ≤ 8 * J * min α (β / D)
  by_cases hle : α ≤ β / D
  · rw [min_eq_left hle]
    exact hab
  · rw [min_eq_right (le_of_not_ge hle)]
    exact hβJ

end Ostmann

end OAI
