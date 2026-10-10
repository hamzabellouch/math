import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-!
# Arbitrary-power decay for radial discarded terms

After rescaling the radial shell variable, a discarded longitudinal edge
has a Fourier frequency bounded below by a positive power of `R`. The
fixed radial cutoff is Schwartz. Its library Fourier seminorm estimates
therefore supply the arbitrary-power error required by `graph:localization`.
The Fourier convention includes `2π`; a fixed conversion of frequency is
absorbed into the displayed constant.
-/

namespace Falconer
open scoped FourierTransform SchwartzMap

theorem schwartz_fourier_decay (Ψ : 𝓢(ℝ, ℂ)) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ ξ : ℝ, r ≤ |ξ| →
      ‖(𝓕 Ψ) ξ‖ ≤ C * r^(-(M : ℝ)) := by
  let C := max 1 ((SchwartzMap.seminorm ℝ M 0) (𝓕 Ψ))
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro r hr ξ hξ
  have hdecay := SchwartzMap.norm_pow_mul_le_seminorm ℝ (𝓕 Ψ) M ξ
  have hproduct : r^M * ‖(𝓕 Ψ) ξ‖ ≤ C := by
    calc
      _ ≤ |ξ|^M * ‖(𝓕 Ψ) ξ‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hξ M) (norm_nonneg _)
      _ ≤ (SchwartzMap.seminorm ℝ M 0) (𝓕 Ψ) := by
        simpa only [Real.norm_eq_abs] using hdecay
      _ ≤ C := le_max_right _ _
  have hb : ‖(𝓕 Ψ) ξ‖ ≤ C / r^M :=
    (le_div_iff₀ (pow_pos hr M)).mpr (by simpa only [mul_comm] using hproduct)
  simpa only [Real.rpow_neg hr.le, Real.rpow_natCast, div_eq_mul_inv] using hb

/-- A fixed positive gain in rescaled phase frequency gives every requested
power of decay by choosing a finite Schwartz seminorm order. -/
theorem radial_nonstationary_arbitrary_power (Ψ : 𝓢(ℝ, ℂ))
    {a : ℝ} (ha : 0 < a) (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ ξ : ℝ, R^a ≤ |ξ| →
      ‖(𝓕 Ψ) ξ‖ ≤ C * R^(-T) := by
  obtain ⟨M, hM⟩ := exists_nat_ge (T / a)
  obtain ⟨C, hC, hdecay⟩ := schwartz_fourier_decay Ψ M
  refine ⟨C, hC, ?_⟩
  intro R hR ξ hξ
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have horder : T ≤ a * (M : ℝ) := by
    have hh := (div_le_iff₀ ha).mp hM
    nlinarith
  have hh := hdecay (R^a) (Real.rpow_pos_of_pos hR0 _) ξ hξ
  have heq : (R^a)^(-(M : ℝ)) = R^(-a * (M : ℝ)) := by
    rw [← Real.rpow_mul hR0.le]
    congr 1
    ring
  rw [heq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hR (by linarith)) hC.le)

end Falconer

end OAI
