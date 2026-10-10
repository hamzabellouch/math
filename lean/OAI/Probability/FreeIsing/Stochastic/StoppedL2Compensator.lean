import OAI.Probability.FreeIsing.Brownian.FiltrationSquare
import OAI.Probability.FreeIsing.Estimates.ContinuousOptionalStopping
import OAI.Probability.FreeIsing.Martingales.StrongMaximal
import OAI.Probability.FreeIsing.Stochastic.StoppedBrownianIntegral

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.ContinuousOptionalStopping

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M A : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

theorem martingale_stopped_compensatedSquare_of_memLp_two
    (hM : Martingale M F μ) (hM2 : ∀ t, MemLp (M t) 2 μ)
    (hcomp : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hprogM : IsStronglyProgressive F M) (hprogA : IsStronglyProgressive F A)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hcA : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω))
    (hA0 : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ A t ω)
    (hAmono : ∀ᵐ ω ∂μ, Monotone (fun t => A t ω))
    (hAint : ∀ t, Integrable (A t) μ)
    (hτ : IsStoppingTime F τ) :
    Martingale (fun t ω => stoppedProcess M τ t ω ^ 2 - stoppedProcess A τ t ω) F μ := by
  have hprog : IsStronglyProgressive F (fun t ω => M t ω ^ 2 - A t ω) := by
    intro t
    exact ((hprogM t).pow 2).sub (hprogA t)
  have hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω ^ 2 - A t ω) := by
    filter_upwards [hcM, hcA] with ω hm ha
    exact (hm.pow 2).sub ha
  apply martingale_stoppedProcess_of_continuous_dominated hcomp hprog hc _ hτ
  intro T
  refine ⟨fun ω => MartingaleStrongMaximal.maximalSquare M T ω + A T ω,
    (MartingaleStrongMaximal.integrable_maximalSquare hM hM2 hcM T).add (hAint T), ?_⟩
  filter_upwards [MartingaleStrongMaximal.ae_all_sq_le_maximalSquare hM hM2 hcM T,
    hA0, hAmono] with ω hmax hpos hmono
  intro t ht
  calc
    |M t ω ^ 2 - A t ω| ≤ |M t ω ^ 2| + |A t ω| := abs_sub _ _
    _ = M t ω ^ 2 + A t ω := by rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (hpos t)]
    _ ≤ _ := add_le_add (hmax t ht) (hmono ht)

end Problem367.ContinuousOptionalStopping

namespace Problem367.BrownianFiltration

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

theorem stopped_square_sub_clock_martingale
    (hB : IsPreBrownianReal B P) (hprog : IsStronglyProgressive F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => B t ω)) (hτ : IsStoppingTime F τ) :
    Martingale (fun t ω => stoppedProcess B τ t ω ^ 2 -
      ((min (t : WithTop ℝ≥0) (τ ω)).untopA : ℝ)) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have htime : IsStronglyProgressive F (fun t (_ : Ω) => (t : ℝ)) := by
    intro t
    let : MeasurableSpace Ω := F t
    apply Measurable.stronglyMeasurable
    fun_prop
  exact ContinuousOptionalStopping.martingale_stopped_compensatedSquare_of_memLp_two
    (martingale_of_independent_past hB hprog.stronglyAdapted hind)
    (fun t => (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two)
    (square_sub_time_martingale hB hprog.stronglyAdapted hind) hprog htime hc
    (Eventually.of_forall (fun ω => NNReal.continuous_coe))
    (Eventually.of_forall (fun ω t => t.coe_nonneg))
    (Eventually.of_forall (fun ω s t hst => by exact_mod_cast hst))
    (fun t => integrable_const (t : ℝ)) hτ

end Problem367.BrownianFiltration

end

end OAI
