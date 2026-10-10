import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DirectionalTransience.StoppedWindow

variable {X A B V F : Type*} [MeasurableSpace X] [MeasurableSpace A]
  [MeasurableSpace B] [MeasurableSpace V] [MeasurableSpace F]

theorem sample_lower_map (μ : Measure X) [IsFiniteMeasure μ]
    (π : Measure V) [IsProbabilityMeasure π]
    (g : X → A) (hg : Measurable g)
    (f : X × V → F) (hf : Measurable f)
    (K : Kernel A B) [IsMarkovKernel K] :
    (((μ.compProd (K.comap g hg)).prod π).map
      (fun p : (X × B) × V => ((g p.1.1,p.1.2),f (p.1.1,p.2)))) =
      (((Kernel.id.prod K) ∥ₖ Kernel.id) ∘ₘ
        ((μ.prod π).map (fun p => (g p.1,f p)))) := by
  have hw : Measurable (fun p : (X × B) × V => ((g p.1.1,p.1.2),f (p.1.1,p.2))) :=
    ((hg.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk
      (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hz : Measurable (fun p : X × V => (g p.1,f p)) := (hg.comp measurable_fst).prodMk hf
  apply Measure.ext_of_lintegral
  intro h hh
  have hhw : Measurable (fun p : (X × B) × V => h ((g p.1.1,p.1.2),f (p.1.1,p.2))) := hh.comp hw
  have hk : Measurable (fun z : A × F => ∫⁻ y, h y ∂((Kernel.id.prod K) ∥ₖ Kernel.id) z) :=
    hh.lintegral_kernel
  have hkm : Measurable (fun p : X × V => ∫⁻ y, h y ∂((Kernel.id.prod K) ∥ₖ Kernel.id) (g p.1,f p)) :=
    hk.comp hz
  rw [lintegral_map hh hw, lintegral_prod _ hhw.aemeasurable,
    Measure.lintegral_compProd hhw.lintegral_prod_right',
    Measure.lintegral_bind (Kernel.aemeasurable _) hh.aemeasurable,
    lintegral_map hk hz, lintegral_prod _ hkm.aemeasurable]
  apply lintegral_congr
  intro x
  simp only [Kernel.comap_apply]
  have hrow : Measurable (fun p : B × V => h ((g x,p.1),f (x,p.2))) :=
    hh.comp ((measurable_const.prodMk measurable_fst).prodMk
      (hf.comp (measurable_const.prodMk measurable_snd)))
  rw [← lintegral_prod _ hrow.aemeasurable, lintegral_prod_symm _ hrow.aemeasurable]
  apply lintegral_congr
  intro v
  rw [Kernel.lintegral_parallelComp _ hh]
  simp_rw [Kernel.id_apply]
  have hi (p : A × B) : (∫⁻ z : F, h (p,z) ∂Measure.dirac (f (x,v))) = h (p,f (x,v)) :=
    lintegral_dirac' _ (hh.comp measurable_prodMk_left)
  simp_rw [hi]
  have hs : Measurable (fun p : A × B => h (p,f (x,v))) := hh.comp measurable_prodMk_right
  simpa only [id_eq, Kernel.id] using
    (Kernel.lintegral_deterministic_prod (f:=id) measurable_id K (g x) hs).symm

end DirectionalTransience.StoppedWindow

end

end OAI
