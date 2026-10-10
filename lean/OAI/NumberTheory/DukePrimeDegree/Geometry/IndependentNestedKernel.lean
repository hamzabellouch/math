import OAI.NumberTheory.DukePrimeDegree.Entropy.NestedRealConditionals

namespace OAI

/-! # The real conditional inside an independent rectangle -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
variable {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]

theorem independent_nested_kernel
    (ρ : Measure (S × (B × ℝ))) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd) :
    ∀ᵐ a ∂(ρ.map MeasurableEquiv.prodAssoc.symm).fst,
      (ρ.map MeasurableEquiv.prodAssoc.symm).condKernel a = (ρ.condKernel a.1).snd := by
  let η := Kernel.prodMkRight B ρ.condKernel.snd
  have hκ (s : S) : (ρ.condKernel.fst ⊗ₖ η) s =
      (ρ.condKernel s).fst.prod (ρ.condKernel s).snd := by
    ext U hU
    rw [Kernel.compProd_apply hU,Measure.prod_apply hU]
    rfl
  have he : ρ.fst ⊗ₘ ρ.condKernel = ρ.fst ⊗ₘ (ρ.condKernel.fst ⊗ₖ η) :=
    Measure.compProd_congr (hp.mono fun s hs => hs.trans (hκ s).symm)
  have hρ : ρ.map MeasurableEquiv.prodAssoc.symm =
      (ρ.fst ⊗ₘ ρ.condKernel.fst) ⊗ₘ η := by
    calc
      _ = (ρ.fst ⊗ₘ ρ.condKernel).map MeasurableEquiv.prodAssoc.symm := by
        rw [Measure.disintegrate]
      _ = (ρ.fst ⊗ₘ (ρ.condKernel.fst ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm := by rw [he]
      _ = _ := Measure.compProd_assoc
  have hf : (ρ.map MeasurableEquiv.prodAssoc.symm).fst = ρ.fst ⊗ₘ ρ.condKernel.fst := by
    rw [hρ,Measure.fst_compProd]
  have H := eq_condKernel_of_measure_eq_compProd η (by rw [hf]; exact hρ)
  exact H.mono fun a ha => ha.symm

 theorem independent_nested_kernel_at_sample
    (ρ : Measure (S × (B × ℝ))) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd) :
    ∀ᵐ z ∂ρ,
      (ρ.map MeasurableEquiv.prodAssoc.symm).condKernel (z.1,z.2.1) =
        (ρ.condKernel z.1).snd := by
  have H := ae_of_ae_map measurable_fst.aemeasurable (independent_nested_kernel ρ hp)
  exact ae_of_ae_map MeasurableEquiv.prodAssoc.symm.measurable.aemeasurable H

end DukePrimeDegree

end

end OAI
