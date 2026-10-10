import OAI.Probability.FreeIsing.Posterior.ContinuousPosteriorInterior
import OAI.Probability.FreeIsing.Posterior.StoppingTimes

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

theorem HasFreeIsingLaw.continuous_posterior_stopping
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ v, IsBrownianReal (B v) (ν v))
    (hmB : ∀ v t, Measurable (B v t))
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace
      ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))))
    {m : TreeVertex d → ℝ≥0 →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ}
    (hma : ∀ v, Adapted F (m v))
    (hcm : ∀ v, ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), Continuous (fun t => m v t p))
    (hversion : ∀ v t, m v t =ᵐ[μ.prod (Measure.infinitePi ν)]
      (fun p => infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))) :
    (∀ v, IsLocalizingSequence F.rightCont
      (PosteriorStoppingTimes.posteriorExit (m v)) (μ.prod (Measure.infinitePi ν))) ∧
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), ∀ v,
      (∀ n t, |stoppedProcess (m v)
          (PosteriorStoppingTimes.posteriorExit (m v) n) t p| ≤
        PosteriorStoppingTimes.threshold n) ∧
      (∀ T : ℝ≥0, ∀ᶠ n in atTop,
        (T : WithTop ℝ≥0) ≤ PosteriorStoppingTimes.posteriorExit (m v) n p) := by
  have hcompact : ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), ∀ v, ∀ T : ℝ≥0,
      ∃ r < (1 : ℝ), ∀ t ≤ T, |m v t p| ≤ r := by
    filter_upwards [hμ.continuous_posterior_compact_localization
      hbeta ν hB hmB hcm hversion] with p hp
    intro v T
    obtain ⟨n, hn⟩ := (hp v T).exists
    exact ⟨PosteriorInteriorLocalization.radius n,
      PosteriorInteriorLocalization.radius_lt_one n, fun t ht => (hn t ht).le⟩
  constructor
  · intro v
    exact PosteriorStoppingTimes.isLocalizingSequence_posteriorExit_rightCont
      (hma v) (hcompact.mono fun p hp => hp v)
  · have hzero := hμ.posterior_version_initial_zero ν
      (fun v => (hB v).toIsPreBrownianReal) (fun v => by
        simpa only [NNReal.coe_zero, zero_mul, zero_add] using hversion v 0)
    filter_upwards [ae_all_iff.mpr hcm, hzero, hcompact] with p hc hz hk
    intro v
    exact ⟨fun n t => PosteriorStoppingTimes.abs_stoppedProcess_le
        (hc v) (hz v).1 n t,
      fun T => PosteriorStoppingTimes.eventually_le_posteriorExit (hk v T)⟩

end Problem367

end

end OAI
