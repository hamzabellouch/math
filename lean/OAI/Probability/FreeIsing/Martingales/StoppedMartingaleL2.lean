import OAI.Probability.FreeIsing.Martingales.RandomEvaluation

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.StoppedMartingaleL2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M L : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

theorem measurable_cappedTime (hτ : IsStoppingTime F τ) (t : ℝ≥0) :
    Measurable (fun ω => (min (t : WithTop ℝ≥0) (τ ω)).untopA) :=
  WithTop.measurable_untopA.comp (measurable_const.min (hτ.measurable.mono hτ.measurableSpace_le le_rfl))

theorem memLp_stoppedProcess_two
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hτ : IsStoppingTime F τ) (t : ℝ≥0) :
    MemLp (stoppedProcess M τ t) 2 μ :=
  MartingaleRandomEvaluation.memLp_random_evaluation hM h2 hc
    (measurable_cappedTime hτ t) (fun _ => WithTop.untopA_le (min_le_left _ _))

theorem integral_stoppedProcess_sq_le
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hτ : IsStoppingTime F τ) {t T : ℝ≥0} (ht : t ≤ T) :
    (∫ ω, (stoppedProcess M τ t ω) ^ 2 ∂μ) ≤ 4 * ∫ ω, (M T ω) ^ 2 ∂μ :=
  MartingaleRandomEvaluation.integral_sq_random_evaluation_le hM h2 hc
    (measurable_cappedTime hτ t)
    (fun _ => (WithTop.untopA_le (min_le_left _ _)).trans ht)

theorem integral_stoppedProcess_sub_sq_le
    (hM : Martingale M F μ) (hL : Martingale L F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hL2 : ∀ t, MemLp (L t) 2 μ)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hcL : ∀ᵐ ω ∂μ, Continuous (fun t => L t ω))
    (hτ : IsStoppingTime F τ) {t T : ℝ≥0} (ht : t ≤ T) :
    (∫ ω, (stoppedProcess M τ t ω - stoppedProcess L τ t ω) ^ 2 ∂μ) ≤
      4 * ∫ ω, (M T ω - L T ω) ^ 2 ∂μ := by
  have hc : ∀ᵐ ω ∂μ, Continuous (fun t => (M - L) t ω) := by
    filter_upwards [hcM, hcL] with ω hm hl
    exact hm.sub hl
  simpa only [stoppedProcess, Pi.sub_apply] using
    integral_stoppedProcess_sq_le (hM.sub hL) (fun t => (hM2 t).sub (hL2 t)) hc hτ ht

theorem tendsto_stoppedProcess_meanSquare
    {N : ℕ → ℝ≥0 → Ω → ℝ}
    (hN : ∀ n, Martingale (N n) F μ) (hL : Martingale L F μ)
    (hN2 : ∀ n t, MemLp (N n t) 2 μ) (hL2 : ∀ t, MemLp (L t) 2 μ)
    (hcN : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t => N n t ω))
    (hcL : ∀ᵐ ω ∂μ, Continuous (fun t => L t ω))
    (τn : ℕ → Ω → WithTop ℝ≥0) (hτn : ∀ n, IsStoppingTime F (τn n))
    {t T : ℝ≥0} (ht : t ≤ T)
    (hlim : Tendsto (fun n => ∫ ω, (N n T ω - L T ω) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω,
      (stoppedProcess (N n) (τn n) t ω - stoppedProcess L (τn n) t ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => integral_nonneg (fun ω => sq_nonneg _))
    (fun n => integral_stoppedProcess_sub_sq_le (hN n) hL
      (hN2 n) hL2 (hcN n) hcL (hτn n) ht)
  simpa only [mul_zero] using hlim.const_mul 4

end Problem367.StoppedMartingaleL2

end

end OAI
