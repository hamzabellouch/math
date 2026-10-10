import OAI.NumberTheory.TwoPointCorrelations.ModFiveZeroTerms

namespace OAI

/-! Uniform logarithmic growth constants for the fixed disk estimate.
These elementary inequalities expose a single constant independent of the
character and the height, ready for the zero-free-region calculation.
-/

namespace TwoPointCorrelations

lemma modFiveLogDerivativeConstant_pos : 0 < modFiveLogDerivativeConstant := by
  have hl : 0 < Real.log ((15 / 16 : ℝ) / (7 / 8)) := Real.log_pos (by norm_num)
  unfold modFiveLogDerivativeConstant
  positivity

lemma modFive_log_height_pos (t : ℝ) : 0 < Real.log (|t| + 2) :=
  Real.log_pos (by linarith [abs_nonneg t])

lemma modFive_log_double_height (t : ℝ) :
    Real.log (|2 * t| + 2) ≤ 2 * Real.log (|t| + 2) := by
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ Real.log ((|t| + 2) ^ 2) := by
      apply Real.log_le_log (by positivity)
      nlinarith [abs_nonneg t, sq_nonneg (|t|)]
    _ = 2 * Real.log (|t| + 2) := by rw [Real.log_pow]; norm_num

lemma modFive_log_disk_growth (t : ℝ) :
    Real.log (8 * modFiveInverseConstant * (|t| + 4)) ≤
      (Real.log (16 * modFiveInverseConstant) / Real.log 2 + 1) *
        Real.log (|t| + 2) := by
  have hK : 1 ≤ modFiveInverseConstant := by
    unfold modFiveInverseConstant
    exact le_add_of_nonneg_right (tsum_nonneg fun _ => norm_nonneg _)
  have hA : 0 < 16 * modFiveInverseConstant := by positivity
  have hlogA : 0 ≤ Real.log (16 * modFiveInverseConstant) :=
    Real.log_nonneg (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hratio : Real.log (16 * modFiveInverseConstant) ≤
      (Real.log (16 * modFiveInverseConstant) / Real.log 2) * Real.log (|t| + 2) := by
    calc
      _ = (Real.log (16 * modFiveInverseConstant) / Real.log 2) * Real.log 2 :=
        (div_mul_cancel₀ _ hlog2.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (div_nonneg hlogA hlog2.le)
  calc
    _ ≤ Real.log ((16 * modFiveInverseConstant) * (|t| + 2)) := by
      apply Real.log_le_log (by positivity)
      nlinarith [mul_nonneg modFiveInverseConstant_pos.le (abs_nonneg t)]
    _ = Real.log (16 * modFiveInverseConstant) + Real.log (|t| + 2) :=
      Real.log_mul hA.ne' (by positivity)
    _ ≤ _ := by nlinarith

/-- One absolute constant controls every nonprincipal modulus-five
logarithmic derivative to the right of one. -/
theorem modFive_logderiv_growth_constant : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ (t : ℝ) (σ : ℝ),
      1 < σ → σ ≤ 2 →
      (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))).re ≤
          C * Real.log (|t| + 2) ∧
      ∀ β : ℝ, 3 / 4 ≤ β → β ≤ 1 →
        DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) = 0 →
        (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))).re ≤
            C * Real.log (|t| + 2) - 1 / (σ - β) := by
  let C := (2 / 3 : ℝ) * modFiveLogDerivativeConstant *
    (Real.log (16 * modFiveInverseConstant) / Real.log 2 + 1)
  have hC : 0 < C := by
    have hD := modFiveLogDerivativeConstant_pos
    have hK := modFiveInverseConstant_pos
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hK1 : 1 ≤ modFiveInverseConstant := by
      unfold modFiveInverseConstant
      exact le_add_of_nonneg_right (tsum_nonneg fun _ => norm_nonneg _)
    have hlogK : 0 ≤ Real.log (16 * modFiveInverseConstant) :=
      Real.log_nonneg (by linarith)
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro χ hχ t σ hσ hσ2
  have hE : (2 / 3 : ℝ) * modFiveLogDerivativeConstant *
      Real.log (8 * modFiveInverseConstant * (|t| + 4)) ≤ C * Real.log (|t| + 2) := by
    dsimp [C]
    calc
      _ ≤ ((2 / 3 : ℝ) * modFiveLogDerivativeConstant) *
          ((Real.log (16 * modFiveInverseConstant) / Real.log 2 + 1) *
            Real.log (|t| + 2)) :=
        mul_le_mul_of_nonneg_left (modFive_log_disk_growth t)
          (mul_nonneg (by norm_num) modFiveLogDerivativeConstant_pos.le)
      _ = _ := by ring
  refine ⟨(modFive_neg_logderiv_re_le χ hχ t hσ hσ2).trans hE, ?_⟩
  intro β hβ hβ1 hzero
  exact (modFive_neg_logderiv_re_le_of_zero χ hχ t hσ hσ2 hβ hβ1 hzero).trans
    (sub_le_sub_right hE _)

end TwoPointCorrelations

end OAI
