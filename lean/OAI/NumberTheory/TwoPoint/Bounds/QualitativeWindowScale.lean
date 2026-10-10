import OAI.NumberTheory.TwoPoint.Bounds.QualitativeShortSums
import OAI.NumberTheory.TwoPoint.Bounds.QualitativeSieveParameters

namespace OAI

/-! The fixed-length MRT error on the interval scales of the qualitative
transfer. Its constants are uniform over the finite set of modified primes. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_qualitative_window_error (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℝ in atTop, ∀ D : ℕ,
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (C₀ * B) →
      Real.log (Real.log (D : ℝ)) / Real.log D ≤
        K * (Real.log B / B ^ (9999 / 10000 : ℝ)) := by
  have hCpos : 0 < C₀ := zero_lt_one.trans_le hC₀
  have hClog : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀
  refine ⟨2 * (Real.log C₀ + 1), by positivity, ?_⟩
  have hlarge := (tendsto_rpow_atTop (show 0 < (9999 / 10000 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop (2 * Real.log 2))
  filter_upwards [eventually_ge_atTop (Real.exp 1), hlarge] with B hB hlargeB
  intro D hDlower hDupper
  have hB₁ : 1 ≤ B := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hB
  have hBp : 0 < B := zero_lt_one.trans_le hB₁
  have hlogB : 1 ≤ Real.log B := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hB
  have hA : 0 < B ^ (9999 / 10000 : ℝ) := Real.rpow_pos_of_pos hBp _
  have hDp : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hDlower
  have hlogDlo : (1 / 2 : ℝ) * B ^ (9999 / 10000 : ℝ) ≤ Real.log D := by
    have ht := Real.log_le_log (by positivity : (0 : ℝ) <
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ))) hDlower
    rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) (Real.exp_ne_zero _),
      Real.log_exp, one_div, Real.log_inv] at ht
    linarith only [ht, hlargeB]
  have hlogDpos : 0 < Real.log (D : ℝ) := lt_of_lt_of_le (by positivity) hlogDlo
  have hlogDhi : Real.log (D : ℝ) ≤ C₀ * B := by
    simpa only [Real.log_exp] using Real.log_le_log hDp hDupper
  have hnum : Real.log (Real.log (D : ℝ)) ≤ (Real.log C₀ + 1) * Real.log B := by
    have ht := Real.log_le_log hlogDpos hlogDhi
    rw [Real.log_mul hCpos.ne' hBp.ne'] at ht
    nlinarith only [ht, hClog, hlogB]
  calc
    _ ≤ ((Real.log C₀ + 1) * Real.log B) / Real.log D :=
      div_le_div_of_nonneg_right hnum hlogDpos.le
    _ ≤ ((Real.log C₀ + 1) * Real.log B) /
        ((1 / 2 : ℝ) * B ^ (9999 / 10000 : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlogDlo
    _ = _ := by ring

/-- The actual progression-window sum, uniformly over every finite-prime
modification, on the manuscript qualitative interval scales. -/
theorem MRTShortExponentialInput.qualitative_window_scale
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (P : Finset ℕ) (D : ℕ), 10 ≤ D →
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (C₀ * B) →
      ∀ᶠ Y : ℕ in atTop, ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
        (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
        ∀ (l : ℕ) [NeZero l] (a : ZMod l) (θ : AddCircle (1 : ℝ)),
        (∑ v ∈ range Y,
          ‖forwardWindowPolynomial (progressionSequence b l a) D (v + 1) θ‖) ≤
          K * D * Y * (Real.log B / B ^ (9999 / 10000 : ℝ)) := by
  obtain ⟨C, hC, hfixed⟩ := hMRT.modified_fixed_windows hfnp hf
  obtain ⟨K, hK, hscale⟩ := eventually_qualitative_window_error C₀ hC₀
  refine ⟨C * (K + 1), by positivity, ?_⟩
  filter_upwards [hscale, eventually_ge_atTop (Real.exp 1)] with B hs hB
  intro P D hD hDlower hDupper
  have hBpos : 0 < B := (Real.exp_pos 1).trans_le hB
  have hlogpos : 0 < Real.log B := by
    have ht : 1 ≤ Real.log B := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hB
    linarith
  have hq : 0 < Real.log B / B ^ (9999 / 10000 : ℝ) := by positivity
  filter_upwards [hfixed P D hD _ hq] with Y hy
  intro b hb hbounded heq l _ a θ
  apply (hy b hb hbounded heq l a θ).trans
  have he := hs D hDlower hDupper
  calc
    _ ≤ C * D * Y *
        (K * (Real.log B / B ^ (9999 / 10000 : ℝ)) +
          Real.log B / B ^ (9999 / 10000 : ℝ)) := by gcongr
    _ = _ := by ring

end TwoPointCorrelations

end OAI
