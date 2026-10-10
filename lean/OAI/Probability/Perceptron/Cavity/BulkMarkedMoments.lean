import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkModel
import OAI.Probability.Perceptron.Interpolation.GaussianReplicaFubini

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def freshMarkedCompactBlockKernel {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r)→ᵇℝ) :
    CompactBlock CompactOverlap r→ᵇℝ :=
  (freshMarkedMatrixKernel Ψ).compContinuous ⟨fun Q => fun i j => (Q i j).val,by fun_prop⟩

lemma freshMarkedCompactBlockKernel_spin {N r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r)→ᵇℝ)
    (x : Fin r→NormalizedSpin N) :
    freshMarkedCompactBlockKernel Ψ (fun i j => bulkOverlap (x i) (x j)) =
      freshMarkedMatrixKernel Ψ (Matrix.gram ℝ (fun i => (x i).val)) := rfl

lemma bulk_twoFresh_block (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F : CompactBlock CompactOverlap r→ᵇℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r)→ᵇℝ) :
    (∫ a, ∫ z, gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) r
      (fun x => F (fun i j => bulkOverlap (x i) (x j))*
        Ψ (gaussianRows (fun i => (x i).val) z.1)*Φ (gaussianRows (fun i => (x i).val) z.2))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin (n+1)))).prod (stdGaussian (EuclideanSpace ℝ (Fin (n+1))))
      ∂bulkDisorderLaw (n+1) M) =
    ∫ Q, (F*freshMarkedCompactBlockKernel Ψ*freshMarkedCompactBlockKernel Φ) (compactBlock r Q)
      ∂bulkGibbsArrayLaw n M f v := by
  rw [bulkGibbsArray_block]
  apply integral_congr_ae
  refine ae_of_all _ fun a => ?_
  have hc : Continuous (fun x : Fin r→NormalizedSpin (n+1) => F (fun i j => bulkOverlap (x i) (x j))) := by
    apply F.continuous.comp
    unfold bulkOverlap spinOverlap
    fun_prop
  have hG := hc.measurable
  have h := gibbs_twoFreshReplica_fubini (unitSphereLaw (n+1))
    ((bulkHamiltonian_continuous (n+1) M f v).measurable.comp (measurable_const.prodMk measurable_id))
    (bulkHamiltonian_exp_integrable n M f v a) (fun x : NormalizedSpin (n+1) => x.val)
    continuous_subtype_val (fun x => F (fun i j => bulkOverlap (x i) (x j))) hG
    (norm_nonneg F) (fun x => F.norm_coe_le_norm _) Ψ Φ
  simpa only [Function.comp_def,id_eq,BoundedContinuousFunction.mul_apply,freshMarkedCompactBlockKernel_spin] using h

lemma bulk_twoFresh_block_tendsto (M : ℕ→ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hν : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) f (v (s n))) atTop (𝓝 ν))
    (r : ℕ) (F : CompactBlock CompactOverlap r→ᵇℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r)→ᵇℝ) :
    Tendsto (fun n => ∫ a, ∫ z, gibbsReplicaMean (unitSphereLaw (s n+1))
      (bulkHamiltonian (s n+1) (M (s n)) f (v (s n)) a.1 a.2) r
      (fun x => F (fun i j => bulkOverlap (x i) (x j))*
        Ψ (gaussianRows (fun i => (x i).val) z.1)*Φ (gaussianRows (fun i => (x i).val) z.2))
      ∂(stdGaussian (EuclideanSpace ℝ (Fin (s n+1)))).prod (stdGaussian (EuclideanSpace ℝ (Fin (s n+1))))
      ∂bulkDisorderLaw (s n+1) (M (s n))) atTop
      (𝓝 (∫ Q, (F*freshMarkedCompactBlockKernel Ψ*freshMarkedCompactBlockKernel Φ) (compactBlock r Q) ∂ν)) := by
  simp_rw [bulk_twoFresh_block]
  exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    ((F*freshMarkedCompactBlockKernel Ψ*freshMarkedCompactBlockKernel Φ).compContinuous
      ⟨compactBlock r,compactBlock_continuous r⟩)).continuousAt.tendsto.comp hν

end SphericalPerceptronFreeEnergy
end

end OAI
