import OAI.NumberTheory.TwoPointCorrelations.ModFiveZeroDistance

namespace OAI

/-! Full logarithmic-derivative control in a narrower zero-free strip.
Jensen counts all nearby zeros, and their proved horizontal separation
bounds the entire pole sum, including at bounded height.
-/

namespace TwoPointCorrelations

open Complex
open scoped Classical

theorem modFive_logderiv_strip_bound : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ (t σ : ℝ),
      1 - c / Real.log (|t| + 2) ≤ σ → σ ≤ 2 →
      DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ)) ≠ 0 ∧
      ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
          C * Real.log (|t| + 2) ^ 2 := by
  obtain ⟨c0, hc0, hfree0⟩ := modFive_nonprincipal_zero_free
  let c := min c0 (1 / 4)
  have hc : 0 < c := lt_min hc0 (by norm_num)
  have hcsmall : c ≤ 1 / 4 := min_le_right _ _
  have hfree : ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ (t β : ℝ),
      1 - c / Real.log (|t| + 2) ≤ β →
      DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
    intro χ hχ t β hβ
    apply hfree0 χ hχ t β
    have hd := div_le_div_of_nonneg_right (min_le_left c0 (1 / 4))
      (modFive_log_height_pos t).le
    linarith
  let P := 1 / Real.log ((15 / 16 : ℝ) / (7 / 8))
  have hP : 0 < P := by dsimp [P]; exact one_div_pos.mpr (Real.log_pos (by norm_num))
  let A := Real.log (16 * modFiveInverseConstant) / Real.log 2 + 1
  have hA : 0 < A := by
    have hK : 1 ≤ modFiveInverseConstant := by
      unfold modFiveInverseConstant
      exact le_add_of_nonneg_right (tsum_nonneg fun _ => norm_nonneg _)
    have hlog : 0 ≤ Real.log (16 * modFiveInverseConstant) := Real.log_nonneg (by linarith)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [A]
    positivity
  let C := A * (2 * modFiveLogDerivativeConstant + 6 * P / c)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos hA (add_pos (mul_pos (by norm_num) modFiveLogDerivativeConstant_pos)
      (div_pos (mul_pos (by norm_num) hP) hc))
  refine ⟨c / 4, C, by positivity, hC, ?_⟩
  intro χ hχ t σ hσ hσ2
  let H := Real.log (|t| + 2)
  have hH : 0 < H := modFive_log_height_pos t
  have hHhalf : 1 / 2 ≤ H := modFive_log_height_ge_half t
  have hσ' : 1 - c / (4 * H) ≤ σ := by
    have he : (c / 4) / H = c / (4 * H) := by ring
    change 1 - (c / 4) / H ≤ σ at hσ
    rwa [he] at hσ
  have hsmall : c / (4 * H) ≤ 1 / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * H)).mpr
    nlinarith
  have hσlow : 7 / 8 ≤ σ := by linarith
  have hne : DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
    apply hfree χ hχ t σ
    have hi : c / (4 * H) ≤ c / H :=
      div_le_div_of_nonneg_left hc.le hH (by linarith)
    linarith
  refine ⟨hne, ?_⟩
  let z := modFiveRealDiskPoint σ
  have hz : ‖z‖ ≤ 3 / 4 := by
    rw [show z = modFiveRealDiskPoint σ from rfl, modFiveRealDiskPoint,
      Complex.norm_real, Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith
  have hp : DirichletCharacter.LFunction χ (modFivePhysicalPoint t z) ≠ 0 := by
    rwa [modFivePhysicalPoint_real]
  have hn : modFiveNormalizedLFunction χ t z ≠ 0 :=
    div_ne_zero hp (χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by norm_num))
  have hd : ∀ ρ ∈ modFiveNormalizedZeros χ t, c / (6 * H) ≤ ‖z - ρ‖ := by
    intro ρ hρ
    exact modFive_zero_distance_of_strip hc hfree χ hχ t σ hσ' hρ
  have he := modFive_normalized_logderiv_norm χ hχ t hz hn
    (show 0 < c / (6 * H) by positivity) hd
  have hcoef : 0 ≤ modFiveLogDerivativeConstant + P / (c / (6 * H)) := by
    exact add_nonneg modFiveLogDerivativeConstant_pos.le (div_nonneg hP.le (by positivity))
  have hlog := mul_le_mul_of_nonneg_left (modFive_log_disk_growth t) hcoef
  have htotal := he.trans hlog
  have hrecip : P / (c / (6 * H)) = (6 * P / c) * H := by
    field_simp
  change _ ≤ (modFiveLogDerivativeConstant + P / (c / (6 * H))) * (A * H) at htotal
  rw [hrecip] at htotal
  have hlinear : H ≤ 2 * H ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlinear
    (mul_nonneg hA.le modFiveLogDerivativeConstant_pos.le)
  have htotal' : ‖deriv (modFiveNormalizedLFunction χ t) z /
      modFiveNormalizedLFunction χ t z‖ ≤ C * H ^ 2 := by
    dsimp [C]
    nlinarith only [htotal, hmul]
  rw [modFiveNormalized_logderiv_eq χ hχ t z hp, norm_mul, modFivePhysicalPoint_real] at htotal'
  norm_num at htotal'
  apply (le_mul_of_one_le_left (norm_nonneg _)
    (by norm_num : (1 : ℝ) ≤ 3 / 2)).trans
  simpa only [norm_div] using htotal'

end TwoPointCorrelations

end OAI
