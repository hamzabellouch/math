import OAI.Probability.FreeIsing.Factors.ContinuousRecovery
import OAI.Probability.FreeIsing.Martingales.StoppedProcessExhaustion

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.StoppedIdentityExhaustion

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_all_stopped_add_of_evaluation
    {X M A : ℝ≥0 → Ω → ℝ} (τ : Ω → WithTop ℝ≥0)
    (hcX : ∀ᵐ ω ∂μ, Continuous (fun t => X t ω))
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hcA : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω))
    (heq : ∀ t, stoppedProcess X τ t =ᵐ[μ]
      fun ω => stoppedProcess M τ t ω + stoppedProcess A τ t ω) :
    ∀ᵐ ω ∂μ, ∀ t, stoppedProcess X τ t ω =
      stoppedProcess M τ t ω + stoppedProcess A τ t ω := by
  have hx := hcX.mono (fun ω hω =>
    StoppedTimePrimitive.continuous_stoppedProcess hω τ)
  have hma : ∀ᵐ ω ∂μ, Continuous (fun t =>
      stoppedProcess M τ t ω + stoppedProcess A τ t ω) := by
    filter_upwards [hcM, hcA] with ω hm ha
    exact (StoppedTimePrimitive.continuous_stoppedProcess hm τ).add
      (StoppedTimePrimitive.continuous_stoppedProcess ha τ)
  have h := ae_eq_of_continuous_of_evaluation_ae_eq hx hma heq
  exact h.mono (fun ω hω t => congrFun hω t)

theorem ae_all_add_of_localizing_stopped_add
    {F : Filtration ℝ≥0 mΩ} {τ : ℕ → Ω → WithTop ℝ≥0}
    {X M A : ℝ≥0 → Ω → ℝ} (hτ : IsLocalizingSequence F τ μ)
    (hcX : ∀ᵐ ω ∂μ, Continuous (fun t => X t ω))
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hcA : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω))
    (heq : ∀ n t, stoppedProcess X (τ n) t =ᵐ[μ]
      fun ω => stoppedProcess M (τ n) t ω + stoppedProcess A (τ n) t ω) :
    ∀ᵐ ω ∂μ, ∀ t, X t ω = M t ω + A t ω := by
  apply StoppedProcessExhaustion.ae_all_add_of_stopped_add
  · intro n
    exact ae_all_stopped_add_of_evaluation (τ n) hcX hcM hcA (heq n)
  · intro N
    filter_upwards [hτ.tendsto_top] with ω hω
    exact ((WithTop.tendsto_nhds_top_iff _).mp hω (N : ℝ≥0)).mono
      (fun n hn => hn.le)

end Problem367.StoppedIdentityExhaustion

end

end OAI
