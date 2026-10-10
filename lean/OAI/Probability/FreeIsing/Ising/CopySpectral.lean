import OAI.Probability.FreeIsing.Ising.CopyStationarity
import OAI.Probability.FreeIsing.Posterior.ObservationLawSpectral

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral

open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem centeredAverage_norm_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ‖TreeLawKoopman.centeredAverage (observationLaw μ)
      (measurePreserving_observationLaw_relabel hμ)‖ ≤
      2 * Real.sqrt ((d : ℝ) - 1) / d := by
  exact observationLaw_centeredAverage_norm_le_critical hμ hd
    (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta).le
    (by simpa only [one_div] using hthreshold)

abbrev differenceSpace (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] :=
  CopyDifference.rangeClosure (CopyDifference.operator
    (measurePreserving_observations (beta := beta) (μ := μ)).1
    (measurePreserving_observations (beta := beta) (μ := μ)).2)

def averageOnDifferences (hμ : HasFreeIsingLaw (Real.tanh beta) μ) :
    differenceSpace beta μ →L[ℝ] differenceSpace beta μ :=
  CopyDifference.averageOnDifferences
    (measurePreserving_observations (beta := beta) (μ := μ)).1
    (measurePreserving_observations (beta := beta) (μ := μ)).2
    (TreeLawKoopman.reflection (A := WienerSampler.Path))
    (fun c => copyRelabel (prefixTreeAut c))
    (fun c => measurePreserving_observationLaw_relabel hμ (prefixTreeAut c))
    (fun c => measurePreserving_copies_relabel hμ (prefixTreeAut c))
    (fun _ => rfl) (fun _ => rfl)

private theorem copyReflection_involutive (c : Fin d) :
    Function.Involutive (copyRelabel (prefixTreeAut c)) := by
  intro p
  exact Prod.ext (TreeLawKoopman.reflection_involutive c p.1)
    (Prod.ext (TreeLawKoopman.reflection_involutive c p.2.1)
      (TreeLawKoopman.reflection_involutive c p.2.2))

theorem averageOnDifferences_isSelfAdjoint
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) :
    IsSelfAdjoint (averageOnDifferences hμ) :=
  CopyDifference.averageOnDifferences_isSelfAdjoint
    (measurePreserving_observations (beta := beta) (μ := μ)).1
    (measurePreserving_observations (beta := beta) (μ := μ)).2
    _ _ _ _ copyReflection_involutive (fun _ => rfl) (fun _ => rfl)

theorem averageOnDifferences_norm_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ‖averageOnDifferences hμ‖ ≤ 2 * Real.sqrt ((d : ℝ) - 1) / d := by
  apply CopyDifference.norm_averageOnDifferences_le
    (measurePreserving_observations (beta := beta) (μ := μ)).1
    (measurePreserving_observations (beta := beta) (μ := μ)).2
    _ _ _ _ TreeLawKoopman.reflection_involutive copyReflection_involutive
    (fun _ => rfl) (fun _ => rfl)
  · positivity
  · exact centeredAverage_norm_le hμ hd hbeta hthreshold

def differenceReflection (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (c : Fin d) :
    differenceSpace beta μ ≃ₗᵢ[ℝ] differenceSpace beta μ :=
  CopyDifference.differenceKoopmanEquiv
    (measurePreserving_observations (beta := beta) (μ := μ)).1
    (measurePreserving_observations (beta := beta) (μ := μ)).2
    (TreeLawKoopman.reflection c) (copyRelabel (prefixTreeAut c))
    (measurePreserving_observationLaw_relabel hμ (prefixTreeAut c))
    (measurePreserving_copies_relabel hμ (prefixTreeAut c))
    rfl rfl (copyReflection_involutive c)

theorem differenceReflection_involutive
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (c : Fin d) :
    Function.Involutive (differenceReflection hμ c) :=
  CopyDifference.differenceKoopmanEquiv_involutive
    (measurePreserving_observations (beta := beta) (μ := μ)).1
    (measurePreserving_observations (beta := beta) (μ := μ)).2
    _ _ _ _ rfl rfl (copyReflection_involutive c)

theorem neighborAverage_differenceReflection
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) :
    ColoredEdgeLifts.neighborAverage (differenceReflection hμ) = averageOnDifferences hμ :=
  CopyDifference.neighborAverage_differenceKoopmanEquiv
    (measurePreserving_observations (beta := beta) (μ := μ)).1
    (measurePreserving_observations (beta := beta) (μ := μ)).2
    _ _ _ _ _ _ _

theorem forwardOperator_pow_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖ColoredEdgeLifts.forwardOperator (by omega : 0 < d)
        (differenceReflection hμ) ((d : ℝ) - 1)⁻¹ ^ n‖ ≤
        K * ((n : ℝ) + 1) * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ n := by
  apply ColoredEdgeLifts.exists_forwardOperator_pow_bound hd _
    (differenceReflection_involutive hμ)
  rw [neighborAverage_differenceReflection]
  exact averageOnDifferences_norm_le hμ hd hbeta hthreshold

theorem summable_forwardOperator_pow
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    Summable (fun n : ℕ => ‖ColoredEdgeLifts.forwardOperator (by omega : 0 < d)
      (differenceReflection hμ) ((d : ℝ) - 1)⁻¹ ^ n‖) := by
  apply ColoredEdgeLifts.summable_norm_forwardOperator_pow hd _
    (differenceReflection_involutive hμ)
  rw [neighborAverage_differenceReflection]
  exact averageOnDifferences_norm_le hμ hd hbeta hthreshold

end Problem367.IsingCopySpectral

end

end OAI
