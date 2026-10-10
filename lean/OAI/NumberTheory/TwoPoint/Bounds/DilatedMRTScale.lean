import OAI.NumberTheory.TwoPoint.Bounds.DilatedShortSums
import OAI.NumberTheory.TwoPoint.Bounds.DilatedWindowParameters
import OAI.NumberTheory.TwoPoint.Bounds.SmoothProductBounds

namespace OAI

/-! The fixed-scale short-sum input for actual dilated factors. Its constant
is independent of the dilation and of the finite set of changed primes. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem MRTShortExponentialInput.dilated_window_scale
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (P : Finset ℕ) (D : ℕ),
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ q : ℕ, 0 < q → ∀ᶠ Y : ℕ in atTop,
      ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
      (∀ p, Nat.Prime p → p ∉ P → b p = f p) → ∀ α : ℝ,
      (∑ v ∈ range Y, ‖shortWindowSum (fun n => b (q * n)) D α v‖) ≤
        C * D * Y * (Real.log B / B ^ (9999 / 10000 : ℝ)) *
          smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hwindow⟩ := hMRT.dilated_short_sums hfnp hf
  let cE := 2 * (Real.log (C₀ + 1) + 2)
  have hcE : 0 < cE := by
    have hh : 0 ≤ Real.log (C₀ + 1) := Real.log_nonneg (by linarith)
    dsimp [cE]
    linarith
  let C' := 4 * C * (cE + 1) + 6
  refine ⟨C', by dsimp [C']; positivity, ?_⟩
  filter_upwards [eventually_dilationWindowParameters C₀ hC₀,
    eventually_ge_atTop (Real.exp 1)] with B hparams hB
  intro P D hDlo hDhi q hq
  have hp := hparams D hDlo hDhi
  have hBp : 0 < B := (Real.exp_pos 1).trans_le hB
  have hlog : 0 < Real.log B := by
    have hh : 1 ≤ Real.log B := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hB
    linarith
  let e := Real.log B / B ^ (9999 / 10000 : ℝ)
  have he : 0 < e := by dsimp [e]; positivity
  have hDpos : 0 < D := hp.cutoff_pos.trans_le hp.cutoff_le
  have hDr : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hM : 1 ≤ smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) :=
    one_le_smoothReciprocalProduct _ (fun _ hx => Nat.prime_of_mem_primeFactors hx) _ (by norm_num)
  filter_upwards [hwindow P q D (dilationCutoff B) hq hp.cutoff_pos hp.cutoff_le
    hp.quotient_ten (cE * e) (by positivity) hp.quotient_error e he] with Y hY
  intro b hb hbb heq α
  have hraw := hY b hb hbb heq α
  have hcoefficient : 4 * C * (cE * e + e) +
      2 * (dilationCutoff B : ℝ) ^ (-(1 / 2) : ℝ) ≤
      (4 * C * (cE + 1) + 4) * e := by
    have ht : (dilationCutoff B : ℝ) ^ (-(1 / 2) : ℝ) ≤ 2 * e := hp.cutoff_tail
    nlinarith
  have hK : (dilationCutoff B : ℝ) ≤ 2 * e * D :=
    (div_le_iff₀ hDr).mp hp.cutoff_relative
  have hboundary : (dilationCutoff B : ℝ) * Y ≤
      2 * D * Y * e * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
    calc
      _ ≤ (2 * e * D) * Y := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg Y)
      _ = 2 * D * Y * e := by ring
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hM
  apply hraw.trans
  calc
    _ ≤ (D : ℝ) * Y * ((4 * C * (cE + 1) + 4) * e *
        smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)) +
        2 * D * Y * e * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
      apply add_le_add _ hboundary
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hcoefficient (by linarith)
    _ = _ := by dsimp [C', e]; ring

end TwoPointCorrelations

end OAI
