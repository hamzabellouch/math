import OAI.NumberTheory.TwoPoint.Bounds.DilatedRoughRight
import OAI.NumberTheory.TwoPoint.Bounds.QualitativeRoughBins

namespace OAI

/-! Actual real bins for the direct dilation estimates, retaining their
single Euler cost for subsequent averaging over padding divisors. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem qualitative_dilated_rough_shifts_real_bins (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (P : Finset ℕ) (M τ : ℝ), 1 < τ → τ < 2 →
      Real.exp (B ^ (9999 / 10000 : ℝ)) / τ ≤ M →
      M ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ q : ℕ, 0 < q → ∀ᶠ Y : ℕ in atTop,
      ∀ b g : ℕ → ℂ, Multiplicative b → OneBounded b → OneBounded g →
      (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
      ∀ (Z : Finset ℕ) (c : ℕ → ℂ),
      (∀ z ∈ Z, M < (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      (∀ z ∈ Z, ‖c z‖ ≤ 1) →
      ‖weightedRoughShiftAverage (fun n => b (q * n)) (fun n => g (q * n)) Z c h Y‖ ≤
        C * B ^ (-11 / 10 : ℝ) * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hrough⟩ := qualitative_dilated_rough_shifts hM hMRT hfnp hf h hh
    (C₀ + 1) (by linarith)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrough, eventually_ge_atTop 1] with B hb hB
  intro P M τ hτ₁ hτ₂ hMlower hMupper q hq
  have hτpos : 0 < τ := zero_lt_one.trans hτ₁
  have hMpos : 0 < M := (div_pos (Real.exp_pos _) hτpos).trans_le hMlower
  have hMc : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
  have hDlower : (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ Nat.ceil M := by
    have ht := (div_le_iff₀ hτpos).mp hMlower
    nlinarith only [ht, hτ₂, hMpos, hMc]
  have hDupper := ceil_exp_scale_bound (B ^ (2 : ℕ)) C₀ M (by nlinarith) hC₀ hMpos.le hMupper
  filter_upwards [hb P (Nat.ceil M) hDlower hDupper q hq] with Y hy
  intro b g hbm hbb hgb heq Z c hZ hc
  apply hy b g hbm hbb hgb heq Z c _ hc
  intro z hz
  have hzw := rough_bin_ceil_window M τ hMpos hτ₂ z ⟨(hZ z hz).1, (hZ z hz).2.1⟩
  exact ⟨hzw.1, hzw.2, (hZ z hz).2.2⟩

theorem qualitative_dilated_rough_shifts_real_bins_right (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (P : Finset ℕ) (M τ : ℝ), 1 < τ → τ < 2 →
      Real.exp (B ^ (9999 / 10000 : ℝ)) / τ ≤ M →
      M ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ q : ℕ, 0 < q → ∀ᶠ Y : ℕ in atTop,
      ∀ b g : ℕ → ℂ, OneBounded b → Multiplicative g → OneBounded g →
      (∀ p, Nat.Prime p → p ∉ P → g p = f p) →
      ∀ (Z : Finset ℕ) (c : ℕ → ℂ),
      (∀ z ∈ Z, M < (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      (∀ z ∈ Z, ‖c z‖ ≤ 1) →
      ‖weightedRoughShiftAverage (fun n => b (q * n)) (fun n => g (q * n)) Z c h Y‖ ≤
        C * B ^ (-11 / 10 : ℝ) * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hrough⟩ := qualitative_dilated_rough_shifts_right hM hMRT hfnp hf h hh
    (C₀ + 1) (by linarith)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrough, eventually_ge_atTop 1] with B hb hB
  intro P M τ hτ₁ hτ₂ hMlower hMupper q hq
  have hτpos : 0 < τ := zero_lt_one.trans hτ₁
  have hMpos : 0 < M := (div_pos (Real.exp_pos _) hτpos).trans_le hMlower
  have hMc : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
  have hDlower : (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ Nat.ceil M := by
    have ht := (div_le_iff₀ hτpos).mp hMlower
    nlinarith only [ht, hτ₂, hMpos, hMc]
  have hDupper := ceil_exp_scale_bound (B ^ (2 : ℕ)) C₀ M (by nlinarith) hC₀ hMpos.le hMupper
  filter_upwards [hb P (Nat.ceil M) hDlower hDupper q hq] with Y hy
  intro b g hbb hgm hgb heq Z c hZ hc
  apply hy b g hbb hgm hgb heq Z c _ hc
  intro z hz
  have hzw := rough_bin_ceil_window M τ hMpos hτ₂ z ⟨(hZ z hz).1, (hZ z hz).2.1⟩
  exact ⟨hzw.1, hzw.2, (hZ z hz).2.2⟩

end TwoPointCorrelations

end OAI
