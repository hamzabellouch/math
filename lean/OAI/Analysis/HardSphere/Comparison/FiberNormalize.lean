import Mathlib

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {W V : Type*} [MeasurableSpace W] [MeasurableSpace V]

def fiberRestrict (κ : Kernel W V) [IsSFiniteKernel κ] (C : Set (W×V)) : Kernel W V :=
  κ.withDensity (fun w v ↦ C.indicator (fun _ ↦ (1 : ℝ≥0∞)) (w,v))

lemma fiberRestrict_apply (κ : Kernel W V) [IsSFiniteKernel κ] {C : Set (W×V)}
    (hC : MeasurableSet C) (w : W) :
    fiberRestrict κ C w=(κ w).restrict {v | (w,v)∈C} := by
  have hm : Measurable (Function.uncurry (fun w : W ↦ fun v : V ↦ C.indicator (fun _ ↦ (1 : ℝ≥0∞)) (w,v))) := by
    change Measurable (C.indicator (fun _ ↦ (1 : ℝ≥0∞)))
    exact measurable_const.indicator hC
  rw [fiberRestrict,Kernel.withDensity_apply _ hm]
  have he : (fun v ↦ C.indicator (fun _ ↦ (1 : ℝ≥0∞)) (w,v))=
      {v | (w,v)∈C}.indicator (fun _ ↦ (1 : ℝ≥0∞)) := rfl
  rw [he]
  have hs : MeasurableSet {v : V | (w,v)∈C} := hC.preimage (measurable_const.prodMk measurable_id)
  exact withDensity_indicator_one hs

def fiberNormalize (κ : Kernel W V) [IsSFiniteKernel κ] (C : Set (W×V)) : Kernel W V where
  toFun w := (fiberRestrict κ C w univ)⁻¹ • fiberRestrict κ C w
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun B hB ↦ ?_
    simp only [Measure.smul_apply,smul_eq_mul]
    exact ((fiberRestrict κ C).measurable_coe MeasurableSet.univ).inv.mul
      ((fiberRestrict κ C).measurable_coe hB)

instance fiberNormalize_finite (κ : Kernel W V) [IsSFiniteKernel κ] (C : Set (W×V)) :
    IsFiniteKernel (fiberNormalize κ C) := ⟨1,by simp,fun w ↦ by
      change ((fiberRestrict κ C w univ)⁻¹ • fiberRestrict κ C w) univ≤1
      rw [Measure.smul_apply,smul_eq_mul]
      exact ENNReal.inv_mul_le_one _⟩

lemma fiberNormalize_mass (κ : Kernel W V) [IsFiniteKernel κ] {C : Set (W×V)}
    (hC : MeasurableSet C) {w : W} (hw : 0<κ w {v | (w,v)∈C}) :
    fiberNormalize κ C w univ=1 := by
  change ((fiberRestrict κ C w univ)⁻¹ • fiberRestrict κ C w) univ=1
  rw [fiberRestrict_apply κ hC,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hw.ne' (measure_ne_top _ _)

lemma fiberNormalize_ac (κ : Kernel W V) [IsFiniteKernel κ] {C : Set (W×V)}
    (hC : MeasurableSet C) (w : W) : fiberNormalize κ C w ≪ κ w := by
  change (fiberRestrict κ C w univ)⁻¹ • fiberRestrict κ C w ≪ κ w
  rw [fiberRestrict_apply κ hC]
  exact Measure.smul_absolutelyContinuous.trans Measure.restrict_le_self.absolutelyContinuous

lemma fiberNormalize_fst (μ : Measure W) [SFinite μ] (κ : Kernel W V) [IsFiniteKernel κ]
    {C : Set (W×V)} (hC : MeasurableSet C)
    (hpos : ∀ᵐ w ∂μ,0<κ w {v | (w,v)∈C}) :
    (μ.compProd (fiberNormalize κ C)).map Prod.fst=μ := by
  ext B hB
  rw [Measure.map_apply measurable_fst hB,Measure.compProd_apply (hB.preimage measurable_fst)]
  have he : (fun w ↦ fiberNormalize κ C w ((fun v ↦ (w,v))⁻¹' (Prod.fst⁻¹' B)))=ᵐ[μ]
      B.indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
    filter_upwards [hpos] with w hw
    by_cases hb : w∈B
    · have hs : (fun v : V ↦ (w,v))⁻¹' (Prod.fst⁻¹' B)=univ := by ext v; simp [hb]
      rw [hs,fiberNormalize_mass κ hC hw,Set.indicator_of_mem hb]
    · have hs : (fun v : V ↦ (w,v))⁻¹' (Prod.fst⁻¹' B)=∅ := by ext v; simp [hb]
      rw [hs,measure_empty,Set.indicator_of_notMem hb]
  rw [lintegral_congr_ae he,lintegral_indicator_const hB,one_mul]

lemma fiberNormalize_compProd_mass (μ : Measure W) [IsProbabilityMeasure μ]
    (κ : Kernel W V) [IsFiniteKernel κ] {C : Set (W×V)} (hC : MeasurableSet C)
    (hpos : ∀ᵐ w ∂μ,0<κ w {v | (w,v)∈C}) :
    μ.compProd (fiberNormalize κ C) univ=1 := by
  have h := congrArg (fun ν : Measure W ↦ ν univ) (fiberNormalize_fst μ κ hC hpos)
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ,measure_univ] using h

end HardSphere.Comparison

end
end

end

end OAI
