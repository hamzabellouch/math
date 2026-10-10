import OAI.Probability.FreeIsing.Estimates.ContinuousOptionalStopping
import OAI.Probability.FreeIsing.Martingales.RightContinuation
import OAI.Probability.FreeIsing.Posterior.ContinuousPosteriorStopping

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

private theorem progressive_rightCont {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : IsStronglyProgressive F M) : IsStronglyProgressive F.rightCont M := by
  intro t
  exact (hM t).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le_rightCont t)))

theorem HasFreeIsingLaw.continuous_posterior_stopped_martingale
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ v, IsBrownianReal (B v) (ν v))
    (hmB : ∀ v t, Measurable (B v t))
    {m : TreeVertex d → ℝ≥0 →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ}
    (hprog : ∀ v, IsStronglyProgressive
      (arrayObservationFiltration B hmB
        (fun (sigma : TreeVertex d → IsingSpin) i => spinSign (sigma i)) measurable_spinSign_array) (m v))
    (hcm : ∀ v, ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), Continuous (fun t => m v t p))
    (hversion : ∀ v t, m v t =ᵐ[μ.prod (Measure.infinitePi ν)]
      (fun p => infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))) :
    let F := arrayObservationFiltration B hmB
      (fun (sigma : TreeVertex d → IsingSpin) i => spinSign (sigma i)) measurable_spinSign_array
    ∀ v, Martingale (m v) F (μ.prod (Measure.infinitePi ν)) ∧
      Martingale (m v) F.rightCont (μ.prod (Measure.infinitePi ν)) ∧
      ∀ n, Martingale
        (stoppedProcess (m v) (PosteriorStoppingTimes.posteriorExit (m v) n))
        F.rightCont (μ.prod (Measure.infinitePi ν)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  let F := arrayObservationFiltration B hmB
    (fun (sigma : TreeVertex d → IsingSpin) i => spinSign (sigma i)) measurable_spinSign_array
  change ∀ v, Martingale (m v) F _ ∧ Martingale (m v) F.rightCont _ ∧ _
  have hce (v : TreeVertex d) (t : ℝ≥0) :
      m v t =ᵐ[μ.prod (Measure.infinitePi ν)]
        (μ.prod (Measure.infinitePi ν))[fun p => spinSign (p.1 v) | F t] := by
    apply (hversion v t).trans
    have h := hμ.infiniteGibbsSpinMean_eq_brownian_past ν
      (fun i => (hB i).toIsPreBrownianReal) hmB t v
    simpa only [F, arrayObservationFiltration, arrayNaturalFiltration_eq_comap,
      plantedArrayObservation, add_comm] using h
  have hmart (v : TreeVertex d) : Martingale (m v) F (μ.prod (Measure.infinitePi ν)) :=
    (martingale_condExp (fun p => spinSign (p.1 v)) F
      (μ.prod (Measure.infinitePi ν))).congr (hprog v).stronglyAdapted
        (fun t => (hce v t).symm)
  have hbound := hμ.continuous_posterior_all_time_field_bound
    hbeta ν hB hmB hcm hversion
  have hb (v : TreeVertex d) : ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      ∀ t, |m v t p| ≤ 1 := by
    filter_upwards [hbound] with p hp
    exact fun t => (abs_lt.mpr ((hp v).1 t).1).le
  have hstop := (hμ.continuous_posterior_stopping hbeta ν hB hmB F
    (fun v => (hprog v).stronglyAdapted.adapted) hcm hversion).1
  intro v
  have hright : Martingale (m v) F.rightCont (μ.prod (Measure.infinitePi ν)) :=
    martingale_rightCont_of_ae_continuous_bounded (hmart v)
      (fun t => (hb v).mono (fun p hp => hp t)) (hcm v)
  refine ⟨hmart v, hright, fun n => ?_⟩
  exact ContinuousOptionalStopping.martingale_stoppedProcess_of_continuous_bounded
    hright (progressive_rightCont (hprog v)) (hcm v) (hb v)
    ((hstop v).isStoppingTime n)

end Problem367

end

end OAI
