import OAI.Probability.FreeIsing.Brownian.SpinRecovery
import OAI.Probability.FreeIsing.Conditioning.Copies
import OAI.Probability.FreeIsing.Ising.ObservationInnovation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationRecovery

open IsingObservationInnovation

def decode {d : ℕ} (x : Paths d) : TreeVertex d → IsingSpin :=
  SpinRecovery.decodeArray (fun v (n : ℕ) => x v n)

theorem measurable_decode {d : ℕ} : Measurable (decode (d := d)) := by
  apply SpinRecovery.measurable_decodeArray.comp
  exact Measurable.of_eval fun v => Measurable.of_eval fun n =>
    (continuous_eval_const (n : ℝ≥0)).measurable.comp (measurable_pi_apply v)

theorem decode_relabel {d : ℕ} (g : TreeAut d) (x : Paths d) :
    decode (relabel g x) = relabel g (decode x) := rfl

theorem decode_uniformObservation_ae {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ] :
    (fun q : IsingInnovation.State d ℝ => decode (uniformObservation q)) =ᵐ[
      μ.prod (labelMeasure d)] Prod.fst := by
  have hnoise := ae_brownian_div_nat_tendsto_zero
    (fun t u => WienerSampler.sample u t)
    WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
  have hall : ∀ᵐ q : IsingInnovation.State d ℝ ∂μ.prod (labelMeasure d),
      ∀ v : TreeVertex d, Tendsto
        (fun n : ℕ => WienerSampler.sample (q.2 v) n / (n : ℝ)) atTop (𝓝 0) := by
    apply ae_all_iff.mpr
    intro v
    exact (planted_noise_coordinate_measurePreserving μ
      (fun _ : TreeVertex d => uniform01) v).quasiMeasurePreserving.ae hnoise
  filter_upwards [hall] with q hq
  funext v
  have h := SpinRecovery.decode_signal_add_noise (q.1 v) (hq v)
  change SpinRecovery.decode (fun n : ℕ => WienerSampler.sample (q.2 v) n +
    ((n : ℝ≥0) : ℝ) * spinSign (q.1 v)) = q.1 v
  have hsign (s : IsingSpin) : SpinRecovery.spinSign s = spinSign s := by
    cases s <;> rfl
  convert h using 1
  congr 1
  funext n
  rw [NNReal.coe_natCast, hsign]
  exact add_comm _ _

theorem map_decode_observationLaw {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ] :
    (observationLaw μ).map decode = μ := by
  rw [observationLaw, Measure.map_map measurable_decode measurable_uniformObservation]
  change Measure.map (fun q => decode (uniformObservation q)) _ = μ
  rw [Measure.map_congr (decode_uniformObservation_ae μ)]
  have : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  simp only [Measure.map_fst_prod, measure_univ, one_smul]

theorem hasFreeIsingLaw_decode_observationLaw {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ) :
    HasFreeIsingLaw theta ((observationLaw μ).map decode) := by
  let := hμ.isProbabilityMeasure
  rw [map_decode_observationLaw μ]
  exact hμ

theorem conditionalCopies_spin_eq_of_observation_eq
    {d : ℕ} {W : Type*} [MeasurableSpace W]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : Measure W) [SFinite ν]
    (κ : Kernel W (IsingInnovation.State d ℝ)) [IsMarkovKernel κ]
    (hmarginal : (ν ⊗ₘ κ).map Prod.snd = μ.prod (labelMeasure d))
    (hobs : ∀ᵐ q ∂ν ⊗ₘ (κ ×ₖ κ),
      uniformObservation q.2.1 = uniformObservation q.2.2) :
    ∀ᵐ q ∂ν ⊗ₘ (κ ×ₖ κ), q.2.1.1 = q.2.2.1 := by
  have hr := decode_uniformObservation_ae μ
  rw [← hmarginal] at hr
  have hj := ae_of_ae_map measurable_snd.aemeasurable hr
  have hfst := (measurePreserving_conditionalCopy_fst ν κ).quasiMeasurePreserving.ae hj
  have hsnd := (measurePreserving_conditionalCopy_snd ν κ).quasiMeasurePreserving.ae hj
  filter_upwards [hfst, hsnd, hobs] with q hq₁ hq₂ hq
  exact hq₁.symm.trans ((congrArg decode hq).trans hq₂)

end Problem367.IsingObservationRecovery

end

end OAI
