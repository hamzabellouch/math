import OAI.Probability.FreeIsing.Ising.ObservationLaw
import OAI.Probability.FreeIsing.Trees.NoisyEdgeDecay

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.IsingObservationInnovation
open PlantedStationarity CopyDifference ColoredEdgeLifts

def uniformObservationChannel (s : IsingSpin) (u : ℝ) : WienerSampler.Path :=
  ⟨fun t => WienerSampler.sample u t + (t : ℝ) * spinSign s,
    (WienerSampler.sample u).continuous.add
      (NNReal.continuous_coe.mul continuous_const)⟩

theorem measurable_uniformObservationChannel :
    Measurable (Function.uncurry uniformObservationChannel) := by
  apply WienerSampler.measurable_path_of_eval
  intro t
  have hs : Measurable spinSign := by intro s hs; trivial
  exact ((continuous_eval_const t).measurable.comp
    (WienerSampler.measurable_sample.comp measurable_snd)).add
    ((hs.comp measurable_fst).const_mul (t : ℝ))

theorem observationLaw_eq_noisyLaw {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) :
    observationLaw μ = NoisyLawSpectral.law μ uniform01 uniformObservationChannel := rfl

variable {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable (hμ : HasFreeIsingLaw theta μ)

theorem observationLaw_centeredAverage_norm_le_critical [IsProbabilityMeasure μ]
    (hd : 3 ≤ d) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hthreshold : theta ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹) :
    ‖TreeLawKoopman.centeredAverage (observationLaw μ)
      (measurePreserving_observationLaw_relabel hμ)‖ ≤
      2 * Real.sqrt ((d : ℝ) - 1) / d :=
  NoisyLawSpectral.centeredAverage_norm_le_critical hμ hd h0 h1 hthreshold
    uniform01 measurable_uniformObservationChannel

variable {π : Measure (Paths d × Paths d)}
variable (hp : MeasurePreserving Prod.fst π (observationLaw μ))
variable (hq : MeasurePreserving Prod.snd π (observationLaw μ))
variable (hπ : ∀ g : TreeAut d, MeasurePreserving
  (Prod.map (relabel g) (relabel g)) π π)

def observationDifferenceReflection (c : Fin d) :
    rangeClosure (operator hp hq) ≃ₗᵢ[ℝ] rangeClosure (operator hp hq) :=
  noisyDifferenceReflection hμ uniform01 measurable_uniformObservationChannel hp hq hπ c

theorem observationLaw_differenceAverage_norm_le_critical
    (hd : 3 ≤ d) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hthreshold : theta ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹) :
    ‖neighborAverage (observationDifferenceReflection hμ hp hq hπ)‖ ≤
      2 * Real.sqrt ((d : ℝ) - 1) / d := by
  change ‖neighborAverage (noisyDifferenceReflection hμ uniform01
    measurable_uniformObservationChannel hp hq hπ)‖ ≤ _
  rw [neighborAverage_noisyDifferenceReflection hμ uniform01
    measurable_uniformObservationChannel hp hq hπ]
  exact noisyAverageOnDifferences_norm_le hμ uniform01
    measurable_uniformObservationChannel hp hq hπ hd h0 h1 hthreshold

theorem observationLaw_forwardOperator_pow_bound
    (hd : 3 ≤ d) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hthreshold : theta ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖forwardOperator (by omega : 0 < d)
        (observationDifferenceReflection hμ hp hq hπ) ((d : ℝ) - 1)⁻¹ ^ n‖ ≤
        K * ((n : ℝ) + 1) * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ n :=
  noisy_forwardOperator_pow_bound hμ uniform01 measurable_uniformObservationChannel
    hp hq hπ hd h0 h1 hthreshold

theorem observationLaw_summable_forwardOperator_pow
    (hd : 3 ≤ d) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hthreshold : theta ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹) :
    Summable (fun n : ℕ => ‖forwardOperator (by omega : 0 < d)
      (observationDifferenceReflection hμ hp hq hπ) ((d : ℝ) - 1)⁻¹ ^ n‖) :=
  summable_noisy_forwardOperator_pow hμ uniform01 measurable_uniformObservationChannel
    hp hq hπ hd h0 h1 hthreshold

end Problem367.IsingObservationInnovation

end

end OAI
