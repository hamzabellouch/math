import Mathlib
import OAI.Probability.Perceptron.Cavity.FreshReplicaKernel
import OAI.Probability.Perceptron.Cavity.FreshThermalLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma compact_moment_limit {a b : ℝ} (μ : ℕ→ProbabilityMeasure (Icc a b))
    (mom : ℕ→ℝ)
    (hmom : ∀ r, Tendsto (fun n => ∫ x, x.val^r ∂(μ n : Measure (Icc a b))) atTop (𝓝 (mom r))) :
    ∃ ν : ProbabilityMeasure (Icc a b), Tendsto μ atTop (𝓝 ν) ∧
      ∀ r, (∫ x, x.val^r ∂(ν : Measure (Icc a b)))=mom r := by
  obtain ⟨ν, -, s, hs, hsub⟩ := isCompact_univ.isSeqCompact (fun n => mem_univ (μ n))
  have hm r : (∫ x, x.val^r ∂(ν : Measure (Icc a b)))=mom r := by
    let F : Icc a b→ᵇℝ := BoundedContinuousFunction.mkOfCompact ⟨fun x => x.val^r,by fun_prop⟩
    have h₁ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).continuousAt.tendsto.comp hsub
    have h₂ := (hmom r).comp hs.tendsto_atTop
    exact tendsto_nhds_unique h₁ h₂
  refine ⟨ν,?_,hm⟩
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  apply integral_continuous_tendsto_of_moments (fun n => (μ n : Measure (Icc a b)))
    (ν : Measure (Icc a b)) (fun r => ?_) F.toContinuousMap
  rw [hm]
  exact hmom r


lemma sourceFresh_exp_ae (n k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) :
    ∀ᵐ a ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw,
      Integrable (fun x => Real.exp (sourceCouplingHamiltonian n k f p d h u a x))
        (sourceFullSpinLeafKernel n k a) := by
  filter_upwards [sourceCoupling_all_exp_ae n k f p d h hh0 hh u 0 z t] with a ha
  simpa only [sourceFullSpinLeafKernel,Kernel.comap_apply,zero_mul,add_zero] using ha 0

def sourceFreshPartitionLaw (n k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) :
    ProbabilityMeasure (FreshPartitionRange f) :=
  freshThermalLaw (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (sourceCouplingHamiltonian n k f p d h u)
    (sourceCouplingHamiltonian_measurable n k f p d h u)
    (fun x => x.1.val) (measurable_subtype_coe.comp measurable_fst) f

def sourceFreshLog (n k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) : ℝ :=
  ∫ a, ∫ g, Real.log (tiltMean (sourceFullSpinLeafKernel n k a)
    (sourceCouplingHamiltonian n k f p d h u a)
    (fun x => Real.exp (f (inner ℝ x.1.val g))) 1)
      ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)))
      ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw

lemma sourceFreshPartitionLaw_moment (n k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) (r : ℕ) :
    (∫ x, x.val^r ∂(sourceFreshPartitionLaw n k f p d h u z t : Measure (FreshPartitionRange f)))=
      sourceFreshMoment n k f (expBCF 1 f) p d h u z t r :=
  freshThermalLaw_moment _ _ _ _ _ _ _ (sourceFresh_exp_ae n k f p d h hh0 hh u z t) r

lemma sourceFreshPartitionLaw_log (n k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) :
    (∫ x, Real.log x.val ∂(sourceFreshPartitionLaw n k f p d h u z t : Measure (FreshPartitionRange f)))=
      sourceFreshLog n k f p d h u z t :=
  freshThermalLaw_log _ _ _ _ _ _ _ (sourceFresh_exp_ae n k f p d h hh0 hh u z t)

theorem sourceFreshLog_tendsto (k : ℕ) (f : ℝ →ᵇℝ)
    (p d : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
    (hh0 : ∀ n i, 0≤h n i) (hh : ∀ n, Monotone (h n))
    (u : (n : ℕ)→Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℕ→ℝ≥0) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∃ η : ProbabilityMeasure (FreshPartitionRange f),
      Tendsto (fun n => sourceFreshPartitionLaw (s n) k f (p (s n)) (d (s n))
        (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 η) ∧
      (∀ r, (∫ x, x.val^r ∂(η : Measure (FreshPartitionRange f)))=
        ∫ Q, freshReplicaArrayKernel (expBCF 1 f) r Q ∂ν) ∧
      Tendsto (fun n => sourceFreshLog (s n) k f (p (s n)) (d (s n))
        (h (s n)) (u (s n)) z (t (s n))) atTop
        (𝓝 (∫ x, Real.log x.val ∂(η : Measure (FreshPartitionRange f)))) := by
  have hmom r := sourceFreshMoment_tendsto k f (expBCF 1 f) p d h hh0 hh u z t s hlim r
  simp_rw [← sourceFreshPartitionLaw_moment _ _ _ _ _ _ (hh0 _) (hh _)] at hmom
  obtain ⟨η,hη,hm⟩ := compact_moment_limit _ _ hmom
  refine ⟨η,hη,hm,?_⟩
  have hlog : Continuous (fun x : FreshPartitionRange f => Real.log x.val) :=
    continuous_subtype_val.log fun x => ne_of_gt ((Real.exp_pos _).trans_le x.prop.1)
  let F : FreshPartitionRange f→ᵇℝ := BoundedContinuousFunction.mkOfCompact ⟨_,hlog⟩
  have ht := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).continuousAt.tendsto.comp hη
  change Tendsto (fun n => ∫ x, Real.log x.val ∂(sourceFreshPartitionLaw (s n) k f (p (s n))
    (d (s n)) (h (s n)) (u (s n)) z (t (s n)) : Measure (FreshPartitionRange f))) atTop _ at ht
  simpa only [F,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,sourceFreshPartitionLaw_log _ _ _ _ _ _ (hh0 _) (hh _)] using ht

end SphericalPerceptronFreeEnergy
end

end OAI
