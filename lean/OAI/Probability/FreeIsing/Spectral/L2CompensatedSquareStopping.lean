import OAI.Probability.FreeIsing.Martingales.DominatedMartingaleRightContinuation
import OAI.Probability.FreeIsing.Martingales.StrongMaximal

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.L2CompensatedSquareStopping

open MartingaleStrongMaximal DominatedMartingaleRightContinuation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M A : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))

include hM h2 hcM

theorem exists_integrable_horizon_envelope (T : ℝ≥0) :
    ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω := by
  refine ⟨fun ω => maximalSquare M T ω + 1,
    (integrable_maximalSquare hM h2 hcM T).add (integrable_const _), ?_⟩
  filter_upwards [ae_all_sq_le_maximalSquare hM h2 hcM T] with ω hω
  intro t ht
  have habs : |M t ω| ≤ M t ω ^ 2 + 1 := by
    nlinarith [sq_nonneg (|M t ω| - 1 / 2), sq_abs (M t ω)]
  exact habs.trans (add_le_add (hω t ht) le_rfl)

theorem martingale_rightCont : Martingale M F.rightCont μ :=
  martingale_rightCont_of_ae_continuous_dominated hM hcM
    (exists_integrable_horizon_envelope hM h2 hcM)

theorem martingale_stoppedProcess_rightCont
    (hprogM : IsStronglyProgressive F M)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ) :
    Martingale (stoppedProcess M τ) F.rightCont μ :=
  DominatedMartingaleRightContinuation.martingale_stoppedProcess_rightCont
    hM hprogM hcM (exists_integrable_horizon_envelope hM h2 hcM) hτ

variable
    (hA0 : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ A t ω)
    (hAmono : ∀ᵐ ω ∂μ, Monotone (fun t => A t ω))
    (hAint : ∀ t, Integrable (A t) μ)

include hA0 hAmono hAint

theorem exists_integrable_compensatedSquare_envelope (T : ℝ≥0) :
    ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω ^ 2 - A t ω| ≤ g ω := by
  refine ⟨fun ω => maximalSquare M T ω + A T ω,
    (integrable_maximalSquare hM h2 hcM T).add (hAint T), ?_⟩
  filter_upwards [ae_all_sq_le_maximalSquare hM h2 hcM T, hA0, hAmono]
    with ω hω ha hm
  intro t ht
  calc
    |M t ω ^ 2 - A t ω| ≤ |M t ω ^ 2| + |A t ω| := abs_sub _ _
    _ = M t ω ^ 2 + A t ω := by
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (ha t)]
    _ ≤ maximalSquare M T ω + A T ω := add_le_add (hω t ht) (hm ht)

variable (hcA : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω))
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)

include hcA hQ

theorem compensatedSquare_martingale_rightCont :
    Martingale (fun t ω => M t ω ^ 2 - A t ω) F.rightCont μ := by
  apply martingale_rightCont_of_ae_continuous_dominated hQ
    (show ∀ᵐ ω ∂μ, Continuous (fun t => M t ω ^ 2 - A t ω) from ?_)
    (exists_integrable_compensatedSquare_envelope hM h2 hcM hA0 hAmono hAint)
  filter_upwards [hcM, hcA] with ω hm ha
  exact (hm.pow 2).sub ha

theorem stopped_compensatedSquare_rightCont
    (hprogM : IsStronglyProgressive F M) (hprogA : IsStronglyProgressive F A)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ) :
    Martingale (fun t ω => stoppedProcess M τ t ω ^ 2 - stoppedProcess A τ t ω)
      F.rightCont μ := by
  have hprog : IsStronglyProgressive F (fun t ω => M t ω ^ 2 - A t ω) := by
    intro t
    exact ((hprogM t).pow 2).sub (hprogA t)
  have hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω ^ 2 - A t ω) := by
    filter_upwards [hcM, hcA] with ω hm ha
    exact (hm.pow 2).sub ha
  exact DominatedMartingaleRightContinuation.martingale_stoppedProcess_rightCont
    hQ hprog hc
    (exists_integrable_compensatedSquare_envelope hM h2 hcM hA0 hAmono hAint) hτ

end Problem367.L2CompensatedSquareStopping

end

end OAI
