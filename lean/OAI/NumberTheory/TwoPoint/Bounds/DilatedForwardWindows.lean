import OAI.NumberTheory.TwoPoint.Bounds.DilatedMRTScale

namespace OAI

/-! Positive-origin Fourier windows for the exact dilated sequence. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma OneBounded.mul_argument {f : ℕ → ℂ} (hf : OneBounded f)
    (q : ℕ) (hq : 0 < q) : OneBounded (fun n => f (q * n)) := by
  intro n hn
  exact hf _ (Nat.mul_pos hq hn)

theorem MRTShortExponentialInput.dilated_forward_windows
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (P : Finset ℕ) (D : ℕ),
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ q : ℕ, 0 < q → ∀ᶠ Y : ℕ in atTop,
      ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
      (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
      ∀ θ : AddCircle (1 : ℝ),
      (∑ v ∈ range Y, ‖forwardWindowPolynomial (fun n => b (q * n)) D (v + 1) θ‖) ≤
        C * D * Y * (Real.log B / B ^ (9999 / 10000 : ℝ)) *
          smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hwindow⟩ := hMRT.dilated_window_scale hfnp hf C₀ hC₀
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hwindow, eventually_ge_atTop 1] with B hB hB1
  intro P D hDlo hDhi q hq
  have ht : Tendsto (fun Y : ℕ => Y + 1) atTop atTop := tendsto_add_atTop_nat 1
  filter_upwards [ht.eventually (hB P D hDlo hDhi q hq),
    eventually_ge_atTop 1] with Y hY hY1
  intro b hb hbb heq θ
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective θ
  simp only [forwardWindowPolynomial_at_real]
  have hs : (∑ v ∈ range Y, ‖shortWindowSum (fun n => b (q * n)) D α (v + 1)‖) ≤
      ∑ v ∈ range (Y + 1), ‖shortWindowSum (fun n => b (q * n)) D α v‖ := by
    rw [sum_range_succ']
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hYr : ((Y + 1 : ℕ) : ℝ) ≤ 2 * Y := by exact_mod_cast (show Y + 1 ≤ 2 * Y by omega)
  have hM := smoothReciprocalProduct_nonneg q.primeFactors
    (fun _ hp => Nat.prime_of_mem_primeFactors hp) (1 / 2) (by norm_num)
  have hE : 0 ≤ Real.log B / B ^ (9999 / 10000 : ℝ) :=
    div_nonneg (Real.log_nonneg hB1) (Real.rpow_nonneg (by linarith) _)
  calc
    _ ≤ _ := hs
    _ ≤ C * D * (Y + 1 : ℕ) * (Real.log B / B ^ (9999 / 10000 : ℝ)) *
        smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := hY b hb hbb heq α
    _ ≤ C * D * (2 * Y) * (Real.log B / B ^ (9999 / 10000 : ℝ)) *
        smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by gcongr
    _ = _ := by ring

end TwoPointCorrelations

end OAI
