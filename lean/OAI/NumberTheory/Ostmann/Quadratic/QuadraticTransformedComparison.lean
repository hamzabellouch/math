import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernelMain
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticTransformedMain

namespace OAI

/-! # The two literal transformed main terms have the required cutoff saving -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap

theorem quadratic_transformed_main_comparison (ρ : 𝓢(ℝ, ℂ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ), 0 < M → ∀ N D K : ℕ,
      Squarefree D → Odd D → 0 < K → ∀ T : ℝ, 0 ≤ T →
      QuadraticSieveBound (K * D ^ 2) N T → ∀ v : ℕ → ℂ,
      ‖quadraticTransformedFirstMain M N D K ρ v -
        quadraticSmallTransformedMain M N D K ρ v‖ ≤
      C * Real.sqrt M * ((K * D ^ 2 : ℕ) : ℝ) ^ ε *
        (N : ℝ) ^ ε * (D : ℝ) ^ ε / Real.sqrt K * T * quadraticSieveEnergy N v := by
  obtain ⟨C₀, hC₀, hc⟩ := quadratic_original_main_comparison ε hε
  let I := ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)
  refine ⟨C₀ * (‖I‖ + 1), by positivity, ?_⟩
  intro M hM N D K hD hDo hK T hT h v
  rw [quadratic_transformed_first_main hM N D K hDo,
    quadratic_small_transformed_main hM N D K hDo, ← mul_sub, norm_mul]
  have hfactor : ‖(Real.sqrt M : ℂ) / 2 * I‖ ≤ Real.sqrt M * (‖I‖ + 1) := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    norm_num only [Complex.norm_ofNat]
    nlinarith [Real.sqrt_nonneg M, norm_nonneg I]
  calc
    _ ≤ (Real.sqrt M * (‖I‖ + 1)) *
        (C₀ * ((K * D ^ 2 : ℕ) : ℝ) ^ ε * (N : ℝ) ^ ε * (D : ℝ) ^ ε /
          Real.sqrt K * T * quadraticSieveEnergy N v) :=
      mul_le_mul hfactor (hc N D K hD hDo hK T hT h v)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
