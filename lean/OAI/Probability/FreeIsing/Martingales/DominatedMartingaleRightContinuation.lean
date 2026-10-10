import OAI.Probability.FreeIsing.Estimates.ContinuousOptionalStopping
import OAI.Probability.FreeIsing.Martingales.RightContinuation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology ENNReal

namespace Problem367.DominatedMartingaleRightContinuation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

omit [IsFiniteMeasure μ] in
theorem tendsto_L1_of_ae_continuous_dominated
    (hint : ∀ t, Integrable (M t) μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω) (s : ℝ≥0) :
    Tendsto (fun t => eLpNorm (M t - M s) 1 μ) (𝓝 s) (𝓝 0) := by
  obtain ⟨g, hg, hgb⟩ := hdom (s + 1)
  have hcont : ContinuousAt (fun t => ∫ ω, ‖M t ω - M s ω‖ ∂μ) s := by
    apply continuousAt_of_dominated
      (Eventually.of_forall (fun t => ((hint t).sub (hint s)).aestronglyMeasurable.norm))
      (bound := fun ω => 2 * g ω)
    · filter_upwards [eventually_lt_nhds (lt_add_one s)] with t ht
      filter_upwards [hgb] with ω hω
      have hst : s ≤ s + 1 := le_add_of_nonneg_right zero_le
      have hb := (norm_sub_le (M t ω) (M s ω)).trans
        (add_le_add (hω t ht.le) (hω s hst))
      simpa only [Pi.sub_apply, norm_norm, two_mul] using hb
    · exact hg.const_mul 2
    · filter_upwards [hc] with ω hω
      exact (hω.sub continuous_const).norm.continuousAt
  have heq (t : ℝ≥0) : eLpNorm (M t - M s) 1 μ =
      ENNReal.ofReal (∫ ω, ‖M t ω - M s ω‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm ((hint t).sub (hint s)).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hint t).sub (hint s))]
    rfl
  simp_rw [heq]
  simpa only [Function.comp_def, sub_self, norm_zero, integral_zero, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.continuousAt.comp hcont).tendsto

theorem martingale_rightCont_of_ae_continuous_dominated
    (hM : Martingale M F μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω) :
    Martingale M F.rightCont μ := by
  apply Problem367.martingale_rightCont_of_L1_rightContinuous hM
  intro s
  exact (tendsto_L1_of_ae_continuous_dominated hM.integrable hc hdom s).mono_left
    nhdsWithin_le_nhds

theorem isStronglyProgressive_mono_filtration
    {G : Filtration ℝ≥0 mΩ} (hFG : F ≤ G) (hM : IsStronglyProgressive F M) :
    IsStronglyProgressive G M := by
  intro t
  exact (hM t).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (hFG t)))

theorem martingale_stoppedProcess_rightCont
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ) :
    Martingale (stoppedProcess M τ) F.rightCont μ :=
  ContinuousOptionalStopping.martingale_stoppedProcess_of_continuous_dominated
    (martingale_rightCont_of_ae_continuous_dominated hM hc hdom)
    (isStronglyProgressive_mono_filtration F.le_rightCont hprog) hc hdom hτ

theorem martingale_stopped_compensatedSquare_rightCont
    {A : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hcomp : Martingale (fun t ω => (M t ω)^2 - A t ω) F μ)
    (hprogM : IsStronglyProgressive F M) (hprogA : IsStronglyProgressive F A)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hcA : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω))
    (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ C)
    (hA0 : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ A t ω)
    (hAmono : ∀ᵐ ω ∂μ, Monotone (fun t => A t ω))
    (hAint : ∀ t, Integrable (A t) μ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ) :
    Martingale (fun t ω => (stoppedProcess M τ t ω)^2 - stoppedProcess A τ t ω)
      F.rightCont μ := by
  have hprog : IsStronglyProgressive F (fun t ω => (M t ω)^2 - A t ω) := by
    intro t
    exact ((hprogM t).pow 2).sub (hprogA t)
  have hc : ∀ᵐ ω ∂μ, Continuous (fun t => (M t ω)^2 - A t ω) := by
    filter_upwards [hcM, hcA] with ω hm ha
    exact (hm.pow 2).sub ha
  apply martingale_stoppedProcess_rightCont hcomp hprog hc _ hτ
  intro T
  refine ⟨fun ω => C^2 + A T ω, (integrable_const _).add (hAint T), ?_⟩
  filter_upwards [hb, hA0, hAmono] with ω hbw hA0w hAmonow
  intro t ht
  have hMsq : (M t ω)^2 ≤ C^2 := by
    have := (sq_le_sq₀ (abs_nonneg (M t ω)) hC).mpr (hbw t)
    simpa only [sq_abs] using this
  calc
    |(M t ω)^2 - A t ω| ≤ |(M t ω)^2| + |A t ω| := abs_sub _ _
    _ = (M t ω)^2 + A t ω := by rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (hA0w t)]
    _ ≤ C^2 + A T ω := add_le_add hMsq (hAmonow ht)

end Problem367.DominatedMartingaleRightContinuation

end

end OAI
