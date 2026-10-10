import Mathlib
import OAI.Probability.Perceptron.Variational.LabelThermalLaw
import OAI.Probability.Perceptron.Cavity.LabelFreshKernel

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma labelProfileField_measurable {S : Type} [MeasurableSpace S] {k : ℕ}
    (q : Fin (k+1)→ℝ) :
    Measurable (Function.uncurry (labelProfileField (S := S) q)) :=
  countableGaussianField_measurable (indexedGaussianRow_measurable _ _ measurable_const)
    (indexedGaussianRowLength_measurable k)

def labelLogResponse {S : Type} {k : ℕ} (q : Fin (k+1)→ℝ)
    (hq1 : q (Fin.last k)≤1) (f : ℝ →ᵇ ℝ) (g : ℕ→ℝ) (x : S×IndexedLeaf k) : ℝ :=
  heatLog ⟨1-q (Fin.last k),sub_nonneg.mpr hq1⟩ 1 f (labelProfileField q g x)

lemma labelLogResponse_measurable {S : Type} [MeasurableSpace S] {k : ℕ}
    (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1) (f : ℝ →ᵇ ℝ) :
    Measurable (Function.uncurry (labelLogResponse (S := S) q hq1 f)) :=
  (heatLog_continuous _ _ f).measurable.comp (labelProfileField_measurable q)

lemma labelLogResponse_bound {S : Type} {k : ℕ} (q : Fin (k+1)→ℝ)
    (hq1 : q (Fin.last k)≤1) (f : ℝ →ᵇ ℝ) (g : ℕ→ℝ) (x : S×IndexedLeaf k) :
    |labelLogResponse q hq1 f g x|≤‖f‖ := heatLog_abs_le _ _ _ _

lemma labelLogResponse_exp {S : Type} {k : ℕ} (q : Fin (k+1)→ℝ)
    (hq1 : q (Fin.last k)≤1) (f : ℝ →ᵇ ℝ) (g : ℕ→ℝ) (x : S×IndexedLeaf k) :
    Real.exp (labelLogResponse q hq1 f g x)=
      gaussianAverageBCF ⟨1-q (Fin.last k),sub_nonneg.mpr hq1⟩ (expBCF 1 f)
        (labelProfileField q g x) := by
  change Real.exp (heatLog ⟨1-q (Fin.last k),sub_nonneg.mpr hq1⟩ 1 f
    (labelProfileField q g x)) = gaussianAverage _ (expBCF 1 f) _
  simpa only [NNReal.coe_one,one_mul] using
    exp_heatLog ⟨1-q (Fin.last k),sub_nonneg.mpr hq1⟩ 1 (by norm_num) f (labelProfileField q g x)

def sourceLabelPartitionLaw (n k : ℕ) (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) : ProbabilityMeasure (FreshPartitionRange ψ) :=
  boundedThermalLaw (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) countableGaussianLaw
    (sourceCouplingHamiltonian n k f p d h u)
    (sourceCouplingHamiltonian_measurable n k f p d h u)
    (labelLogResponse q hq1 ψ) (labelLogResponse_measurable q hq1 ψ) ψ

def sourceLabelFreshLog (n k : ℕ) (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) : ℝ :=
  ∫ a, ∫ g, Real.log (tiltMean (sourceFullSpinLeafKernel n k a)
    (sourceCouplingHamiltonian n k f p d h u a)
    (fun x => gaussianAverageBCF ⟨1-q (Fin.last k),sub_nonneg.mpr hq1⟩ (expBCF 1 ψ)
      (labelProfileField q g x)) 1) ∂countableGaussianLaw
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw

lemma sourceLabelPartitionLaw_moment (n k : ℕ) (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ)
    (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) (r : ℕ) :
    (∫ x, x.val^r ∂(sourceLabelPartitionLaw n k q hq1 f ψ p d h u z t :
      Measure (FreshPartitionRange ψ)))=
        sourceLabelFreshMoment n k q hq1 f (expBCF 1 ψ) p d h u z t r := by
  have hm := boundedThermalLaw_moment (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) countableGaussianLaw
    (sourceCouplingHamiltonian n k f p d h u)
    (sourceCouplingHamiltonian_measurable n k f p d h u)
    (labelLogResponse q hq1 ψ) (labelLogResponse_measurable q hq1 ψ) ψ
    (labelLogResponse_bound q hq1 ψ) (sourceFresh_exp_ae n k f p d h hh0 hh u z t) r
  simpa only [sourceLabelPartitionLaw,sourceLabelFreshMoment,labelLogResponse_exp] using hm

lemma sourceLabelPartitionLaw_log (n k : ℕ) (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ)
    (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) :
    (∫ x, Real.log x.val ∂(sourceLabelPartitionLaw n k q hq1 f ψ p d h u z t :
      Measure (FreshPartitionRange ψ)))=sourceLabelFreshLog n k q hq1 f ψ p d h u z t := by
  have hm := boundedThermalLaw_log (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) countableGaussianLaw
    (sourceCouplingHamiltonian n k f p d h u)
    (sourceCouplingHamiltonian_measurable n k f p d h u)
    (labelLogResponse q hq1 ψ) (labelLogResponse_measurable q hq1 ψ) ψ
    (labelLogResponse_bound q hq1 ψ) (sourceFresh_exp_ae n k f p d h hh0 hh u z t)
  simpa only [sourceLabelPartitionLaw,sourceLabelFreshLog,labelLogResponse_exp] using hm

theorem sourceLabelFreshLog_tendsto (k : ℕ) (q : Fin (k+1)→ℝ)
    (h0 : 0≤q 0) (hq : Monotone q) (h1 : q (Fin.last k)≤1) (f ψ : ℝ →ᵇ ℝ)
    (p d : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
    (hh0 : ∀ n i, 0≤h n i) (hh : ∀ n, Monotone (h n))
    (u : (n : ℕ)→Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℕ→ℝ≥0) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∃ η : ProbabilityMeasure (FreshPartitionRange ψ),
      Tendsto (fun n => sourceLabelPartitionLaw (s n) k q h1 f ψ (p (s n)) (d (s n))
        (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 η) ∧
      (∀ r, (∫ x, x.val^r ∂(η : Measure (FreshPartitionRange ψ)))=
        ∫ Q, labelFreshArrayKernel q (expBCF 1 ψ) r Q ∂ν) ∧
      Tendsto (fun n => sourceLabelFreshLog (s n) k q h1 f ψ (p (s n)) (d (s n))
        (h (s n)) (u (s n)) z (t (s n))) atTop
        (𝓝 (∫ x, Real.log x.val ∂(η : Measure (FreshPartitionRange ψ)))) := by
  have hmom r := sourceLabelFreshMoment_tendsto k q h0 hq h1 f (expBCF 1 ψ)
    p d h hh0 hh u z t s hlim r
  simp_rw [← sourceLabelPartitionLaw_moment _ _ _ _ _ _ _ _ _ (hh0 _) (hh _)] at hmom
  obtain ⟨η,hη,hm⟩ := compact_moment_limit _ _ hmom
  refine ⟨η,hη,hm,?_⟩
  let F : FreshPartitionRange ψ→ᵇℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => Real.log x.val, continuous_subtype_val.log fun x =>
      ne_of_gt ((Real.exp_pos _).trans_le x.prop.1)⟩
  have ht := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).continuousAt.tendsto.comp hη
  change Tendsto (fun n => ∫ x, Real.log x.val ∂(sourceLabelPartitionLaw (s n) k q h1 f ψ (p (s n))
    (d (s n)) (h (s n)) (u (s n)) z (t (s n)) : Measure (FreshPartitionRange ψ))) atTop _ at ht
  simpa only [F,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,
    sourceLabelPartitionLaw_log _ _ _ _ _ _ _ _ _ (hh0 _) (hh _)] using ht

end SphericalPerceptronFreeEnergy
end

end OAI
