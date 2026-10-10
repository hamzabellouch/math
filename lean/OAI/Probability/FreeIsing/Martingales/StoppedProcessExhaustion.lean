import OAI.Probability.FreeIsing.Martingales.StoppedTimePrimitive

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367.StoppedProcessExhaustion

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_all_eq_of_stopped_eq
    {X Y : ℝ≥0 → Ω → E} {τ : ℕ → Ω → WithTop ℝ≥0}
    (heq : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      stoppedProcess X (τ n) t ω = stoppedProcess Y (τ n) t ω)
    (hexit : ∀ N : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      ((N : ℝ≥0) : WithTop ℝ≥0) ≤ τ n ω) :
    ∀ᵐ ω ∂μ, ∀ t, X t ω = Y t ω := by
  filter_upwards [ae_all_iff.mpr heq, ae_all_iff.mpr hexit] with ω he hx
  intro t
  obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
  obtain ⟨n, hn⟩ := (hx N).exists
  have ht : (t : WithTop ℝ≥0) ≤ τ n ω :=
    (WithTop.coe_le_coe.mpr (show t ≤ (N : ℝ≥0) from hN)).trans hn
  simpa only [stoppedProcess_eq_of_le ht] using he n t

theorem ae_all_add_of_stopped_add
    {X M A : ℝ≥0 → Ω → ℝ} {τ : ℕ → Ω → WithTop ℝ≥0}
    (heq : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      stoppedProcess X (τ n) t ω =
        stoppedProcess M (τ n) t ω + stoppedProcess A (τ n) t ω)
    (hexit : ∀ N : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      ((N : ℝ≥0) : WithTop ℝ≥0) ≤ τ n ω) :
    ∀ᵐ ω ∂μ, ∀ t, X t ω = M t ω + A t ω :=
  ae_all_eq_of_stopped_eq (Y := fun t ω => M t ω + A t ω) heq hexit

end Problem367.StoppedProcessExhaustion

end

end OAI
