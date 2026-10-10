import OAI.NumberTheory.TwoPoint.Bounds.WindowPolynomialBounds

namespace OAI

/-! The precise MRT input on actual progression windows, uniformly over
all multiplicative finite-prime changes of the original nonpretentious factor. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem MRTShortExponentialInput.modified_windows
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (D : ℕ), 10 ≤ D → ∀ M : ℝ,
      ∀ᶠ Y : ℕ in atTop, ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
        (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
        ∀ (l : ℕ) [NeZero l] (a : ZMod l) (θ : AddCircle (1 : ℝ)),
        (∑ v ∈ range Y,
          ‖forwardWindowPolynomial (progressionSequence b l a) D (v + 1) θ‖) /
            ((D : ℝ) * (Y + 1 : ℕ)) ≤
          C * (Real.exp (-M / 20) + mrtShortError (Y + 1) D) := by
  obtain ⟨C, hC, hbound⟩ := hMRT
  refine ⟨C, hC, ?_⟩
  intro P D hD M
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hfnp.eventually_mrt_lower_bound hf P D M)
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop D] with Y hYN hYD
  intro b hb hbounded heq l _ a θ
  have hdist := hN₀ (Y + 1) (by omega) b hbounded heq
  have hDr : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hYr : (0 : ℝ) < (Y + 1 : ℕ) := by positivity
  apply (div_le_iff₀ (mul_pos hDr hYr)).mpr
  have hh := progression_window_sum_from_integral b D Y l a
    (C * (D : ℝ) * (Y + 1 : ℕ) *
      (Real.exp (-M / 20) + mrtShortError (Y + 1) D))
    (fun α => hbound (Y + 1) D hD (by omega) b hb hbounded M hdist α) θ
  convert hh using 1
  ring

end TwoPointCorrelations

end OAI
