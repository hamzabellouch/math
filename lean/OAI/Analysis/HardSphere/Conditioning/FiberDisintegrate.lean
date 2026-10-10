import Mathlib
import OAI.Analysis.HardSphere.Comparison.FiberNormalize

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {W V : Type*} [MeasurableSpace W] [MeasurableSpace V]

lemma fiberRestrict_le (κ : Kernel W V) [IsFiniteKernel κ] {C : Set (W×V)} (hC : MeasurableSet C) (w : W) :
    fiberRestrict κ C w≤κ w := by rw [fiberRestrict_apply κ hC]; exact Measure.restrict_le_self

lemma exposed_mass_positive (μ : Measure W) (κ : Kernel W V) [IsFiniteKernel κ]
    {C : Set (W×V)} (hC : MeasurableSet C) :
    ∀ᵐ w ∂μ.withDensity (fun w ↦ fiberRestrict κ C w univ),0<κ w {v | (w,v)∈C} := by
  rw [ae_withDensity_iff ((fiberRestrict κ C).measurable_coe MeasurableSet.univ)]
  exact ae_of_all _ fun w hw ↦ by
    rw [fiberRestrict_apply κ hC,Measure.restrict_apply_univ] at hw
    exact pos_iff_ne_zero.mpr hw

lemma fiber_rescale (κ : Kernel W V) [IsFiniteKernel κ] {C : Set (W×V)}
    (hC : MeasurableSet C) (w : W) (B : Set V) :
    (fiberRestrict κ C w univ) * (fiberNormalize κ C w B)=fiberRestrict κ C w B := by
  change (fiberRestrict κ C w univ) * (((fiberRestrict κ C w univ)⁻¹ • fiberRestrict κ C w) B)=_
  rw [Measure.smul_apply,smul_eq_mul,←mul_assoc]
  by_cases hz : fiberRestrict κ C w univ=0
  · have h0 : fiberRestrict κ C w=0 := Measure.measure_univ_eq_zero.mp hz
    simp [h0]
  · have hfin : fiberRestrict κ C w univ≠⊤ := ne_of_lt ((fiberRestrict_le κ hC w univ).trans_lt (measure_lt_top _ _))
    rw [ENNReal.mul_inv_cancel hz hfin,one_mul]

lemma fiber_disintegrate (μ : Measure W) [SFinite μ] (κ : Kernel W V) [IsFiniteKernel κ]
    {C : Set (W×V)} (hC : MeasurableSet C)
    [SFinite (μ.withDensity (fun w ↦ fiberRestrict κ C w univ))] :
    (μ.withDensity (fun w ↦ fiberRestrict κ C w univ)).compProd (fiberNormalize κ C)=
      (μ.compProd κ).restrict C := by
  ext B hB
  rw [Measure.compProd_apply hB,lintegral_withDensity_eq_lintegral_mul₀]
  · simp only [Pi.mul_apply]
    simp_rw [fiber_rescale κ hC]
    rw [Measure.restrict_apply hB,Measure.compProd_apply (hB.inter hC)]
    apply lintegral_congr
    intro w
    have hBw : MeasurableSet (Prod.mk w ⁻¹' B) := hB.preimage (measurable_const.prodMk measurable_id)
    rw [fiberRestrict_apply κ hC,Measure.restrict_apply hBw]
    rfl
  · exact ((fiberRestrict κ C).measurable_coe MeasurableSet.univ).aemeasurable
  · exact ((fiberNormalize κ C).measurable_kernel_prodMk_left hB).aemeasurable

end HardSphere.Comparison

end
end

end

end OAI
