import Mathlib
import OAI.Probability.Perceptron.Cavity.FreshThermalLaw
import OAI.Probability.Perceptron.Cavity.FreshGGUniqueness

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma probability_Icc_eq_of_moments {a b : ℝ} (μ ν : ProbabilityMeasure (Icc a b))
    (hm : ∀ r : ℕ, (∫ x, x.val^r ∂(μ : Measure (Icc a b)))=
      ∫ x, x.val^r ∂(ν : Measure (Icc a b))) : μ=ν := by
  have h : Tendsto (fun _ : ℕ => μ) atTop (𝓝 ν) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro F
    apply integral_continuous_tendsto_of_moments (fun _ : ℕ => (μ : Measure (Icc a b)))
      (ν : Measure (Icc a b)) (fun r => ?_) F.toContinuousMap
    rw [hm r]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique tendsto_const_nhds h

variable (μ ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
variable (hGGμ : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
  (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0)
variable (hGGν : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
  (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν n i f g=0)
variable (hμ : ∀ᵐ Q ∂(μ : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
variable (hν : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
variable (hpair : (μ : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
  (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1))
variable (f : ℝ →ᵇ ℝ) (η ξ : ProbabilityMeasure (FreshPartitionRange f))
variable (hη : ∀ r, (∫ x, x.val^r ∂(η : Measure (FreshPartitionRange f)))=
  ∫ Q, freshReplicaArrayKernel (expBCF 1 f) r Q ∂(μ : Measure (CompactArray CompactJointOverlap)))
variable (hξ : ∀ r, (∫ x, x.val^r ∂(ξ : Measure (FreshPartitionRange f)))=
  ∫ Q, freshReplicaArrayKernel (expBCF 1 f) r Q ∂(ν : Measure (CompactArray CompactJointOverlap)))

include hGGμ hGGν hμ hν hpair hη hξ in
theorem freshPartitionLaw_eq_of_pair_law : η=ξ := by
  apply probability_Icc_eq_of_moments
  intro r
  rw [hη r,hξ r]
  exact freshReplicaKernel_eq_of_pair_law μ ν hGGμ hGGν hμ hν hpair (expBCF 1 f) r

include hGGμ hGGν hμ hν hpair hη hξ in
theorem freshLog_eq_of_pair_law :
    (∫ x, Real.log x.val ∂(η : Measure (FreshPartitionRange f)))=
      ∫ x, Real.log x.val ∂(ξ : Measure (FreshPartitionRange f)) := by
  rw [freshPartitionLaw_eq_of_pair_law μ ν hGGμ hGGν hμ hν hpair f η ξ hη hξ]

end SphericalPerceptronFreeEnergy
end

end OAI
