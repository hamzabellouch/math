import Mathlib
import OAI.Analysis.HardSphere.Kernels.TrialKernel

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Comparison
variable {U X : Type*} [MeasurableSpace U] [MeasurableSpace X]

lemma successKernel_restrict_le (κ : Kernel U X) [IsFiniteKernel κ] (S : Set X) (hS : MeasurableSet S)
    {u : U} {c : ℝ≥0∞} (hc : c≤κ u S) :
    successKernel κ S hS u≤c⁻¹ • (κ u).restrict S := by
  rw [successKernel_apply]
  intro B
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul_left (ENNReal.inv_le_inv.mpr hc) _

lemma successful_marginal_le (μ ν : Measure U) [SFinite μ] [SFinite ν]
    (κ : Kernel U X) [IsFiniteKernel κ] (S : Set X) (hS : MeasurableSet S)
    {c A : ℝ≥0∞} (hμ : μ≤A • ν) (hc : ∀ᵐu ∂μ,c≤κ u S) :
    (μ.compProd (successKernel κ S hS)).map Prod.snd ≤
      (c⁻¹*A) • (((ν.compProd κ).map Prod.snd).restrict S) := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.map_apply measurable_snd hB,Measure.compProd_apply (hB.preimage measurable_snd),
    Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hB,
    Measure.map_apply measurable_snd (hB.inter hS),Measure.compProd_apply ((hB.inter hS).preimage measurable_snd)]
  calc
    _ ≤ ∫⁻u,c⁻¹*(κ u (B∩S)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hc] with u hu
      change successKernel κ S hS u B≤_
      simpa only [preimage_preimage,preimage_id,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hB] using
        successKernel_restrict_le κ S hS hu B
    _ = c⁻¹*(∫⁻u,κ u (B∩S) ∂μ) := lintegral_const_mul _ (κ.measurable_coe (hB.inter hS))
    _ ≤ c⁻¹*(∫⁻u,κ u (B∩S) ∂A • ν) := mul_le_mul_right (lintegral_mono' hμ le_rfl) _
    _ = _ := by rw [lintegral_smul_measure]; simp only [smul_eq_mul]; rw [mul_assoc]; rfl

lemma normalizer_positive_of_uniform_success (μ ν : Measure U) [IsProbabilityMeasure μ] [SFinite ν]
    (κ : Kernel U X) [IsFiniteKernel κ] (S : Set X) (hS : MeasurableSet S)
    {c A : ℝ≥0∞} (hc0 : 0<c) (hA : A≠⊤) (hμ : μ≤A • ν)
    (hc : ∀ᵐu ∂μ,c≤κ u S) : 0<((ν.compProd κ).map Prod.snd) S := by
  rw [Measure.map_apply measurable_snd hS,Measure.compProd_apply (hS.preimage measurable_snd)]
  have h₁ : c≤∫⁻u,κ u S ∂μ := by
    calc
      _ = ∫⁻_u,c ∂μ := by simp
      _ ≤ _ := lintegral_mono_ae hc
  have h₂ : (∫⁻u,κ u S ∂μ)≤A*(∫⁻u,κ u S ∂ν) := by
    convert lintegral_mono' hμ (f:=fun u ↦ κ u S) le_rfl using 1
    rw [lintegral_smul_measure,smul_eq_mul]
  change 0<(∫⁻u,κ u S ∂ν)
  exact (ENNReal.div_pos hc0.ne' hA).trans_le (ENNReal.div_le_of_le_mul' (h₁.trans h₂))

lemma restricted_le_normalized (P : Measure X) [IsProbabilityMeasure P] (S : Set X) :
    P.restrict S≤(P S)⁻¹ • P.restrict S := by
  intro B
  rw [Measure.smul_apply,smul_eq_mul]
  have hi : (1:ℝ≥0∞)≤(P S)⁻¹ := by
    simpa using ENNReal.inv_le_inv.mpr (prob_le_one (μ:=P) (s:=S))
  simpa using mul_le_mul_left hi (P.restrict S B)

lemma successful_marginal_le_reference (μ ν : Measure U) [SFinite μ] [IsProbabilityMeasure ν]
    (κ : Kernel U X) [IsMarkovKernel κ] (S : Set X) (hS : MeasurableSet S)
    {c A : ℝ≥0∞} (hμ : μ≤A • ν) (hc : ∀ᵐu ∂μ,c≤κ u S) :
    (μ.compProd (successKernel κ S hS)).map Prod.snd ≤
      (c⁻¹*A) • ((((ν.compProd κ).map Prod.snd) S)⁻¹ • (((ν.compProd κ).map Prod.snd).restrict S)) := by
  have := successful_marginal_le μ ν κ S hS hμ hc
  refine this.trans ?_
  intro B
  simpa only [Measure.smul_apply,smul_eq_mul] using mul_le_mul_right (restricted_le_normalized ((ν.compProd κ).map Prod.snd) S B) (c⁻¹*A)

end HardSphere.Comparison

end
end

end

end OAI
