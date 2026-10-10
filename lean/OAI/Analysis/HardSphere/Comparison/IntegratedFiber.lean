import Mathlib

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {W A B : Type*} [MeasurableSpace W] [MeasurableSpace A] [MeasurableSpace B]

lemma integrated_primary_density (ξ : Measure W) [SFinite ξ]
    (κ : Kernel W A) (η : Kernel W B) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (f : A→B) (hf : Measurable f) (L : W×B→ℝ≥0∞) (hL : Measurable L)
    (h : ∀ᵐw ∂ξ,(κ w).map f=(η w).withDensity (fun b ↦ L (w,b))) :
    (ξ.compProd κ).map (fun p ↦ (p.1,f p.2))=(ξ.compProd η).withDensity L := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hm : Measurable (fun p : W×A ↦ (p.1,f p.2)) := measurable_fst.prodMk (hf.comp measurable_snd)
  rw [lintegral_map hF hm,Measure.lintegral_compProd (show Measurable (fun p : W×A ↦ F (p.1,f p.2)) from hF.comp hm),
    lintegral_withDensity_eq_lintegral_mul _ hL hF,
    Measure.lintegral_compProd (hL.mul hF)]
  apply lintegral_congr_ae
  filter_upwards [h] with w hw
  rw [←lintegral_map (show Measurable (fun b : B ↦ F (w,b)) from hF.comp measurable_prodMk_left) hf,hw,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun b : B ↦ L (w,b)) from hL.comp measurable_prodMk_left)
      (show Measurable (fun b : B ↦ F (w,b)) from hF.comp measurable_prodMk_left)]
  rfl

lemma map_density_comp (μ : Measure A) (f : A→B) (hf : Measurable f)
    (L : B→ℝ≥0∞) (hL : Measurable L) :
    (μ.withDensity (L∘f)).map f=(μ.map f).withDensity L := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hf]
  change (∫⁻a,(F∘f) a ∂μ.withDensity (L∘f))=_
  rw [lintegral_withDensity_eq_lintegral_mul _ (hL.comp hf) (hF.comp hf),
    lintegral_withDensity_eq_lintegral_mul _ hL hF,lintegral_map (hL.mul hF) hf]
  rfl

end HardSphere.Comparison

end
end

end

end OAI
