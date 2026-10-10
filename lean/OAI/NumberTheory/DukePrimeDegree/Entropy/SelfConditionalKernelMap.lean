import OAI.NumberTheory.DukePrimeDegree.Entropy.SelfConditionalKernel
import OAI.NumberTheory.DukePrimeDegree.Dynamics.KernelStabilizerMeasurable

namespace OAI

/-! # Transporting self-consistency through measurable coordinates -/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace DukePrimeDegree

theorem measurableSet_kernel_selfConstant {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace Y] (κ : Kernel Y Y) [IsMarkovKernel κ] :
    MeasurableSet {x | ∀ᵐ y ∂κ x, κ y=κ x} := by
  have hrel : MeasurableSet {z : Y × Y | κ z.2=κ z.1} :=
    measurableSet_finite_kernel_eq (κ.comap Prod.snd measurable_snd)
      (κ.comap Prod.fst measurable_fst)
  have hm : Measurable (fun x => κ x {y | κ y≠κ x}) :=
    Kernel.measurable_kernel_prodMk_left hrel.compl
  have he : {x | ∀ᵐ y ∂κ x, κ y=κ x} = {x | κ x {y | κ y≠κ x}=0} := by
    ext x
    exact ae_iff
  rw [he]
  exact measurableSet_eq_fun hm measurable_const

/-- No global injectivity of the coordinate map is required. The actual
ambient kernel must agree almost everywhere with the pushed local kernel. -/
theorem selfConstant_kernel_map
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y] [StandardBorelSpace Y]
    (ρ : Measure Z) (η : Kernel Z Z) [IsMarkovKernel η]
    (hstat : ρ.bind η=ρ)
    (hself : ∀ᵐ z ∂ρ, ∀ᵐ w ∂η z, η w=η z)
    (F : Z → Y) (hF : Measurable F)
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (hversion : ∀ᵐ z ∂ρ, κ (F z)=(η z).map F) :
    ∀ᵐ x ∂ρ.map F, ∀ᵐ y ∂κ x, κ y=κ x := by
  have hv : ∀ᵐ z ∂ρ, ∀ᵐ w ∂η z, κ (F w)=(η w).map F := by
    apply Measure.ae_ae_of_ae_bind η.measurable.aemeasurable
    rwa [hstat]
  apply (ae_map_iff hF.aemeasurable (measurableSet_kernel_selfConstant κ)).mpr
  filter_upwards [hversion,hself,hv] with z hz hs hvz
  rw [hz]
  have hset : MeasurableSet {y | κ y=(η z).map F} :=
    measurableSet_finite_kernel_eq κ (Kernel.const Y ((η z).map F))
  apply (ae_map_iff hF.aemeasurable hset).mpr
  filter_upwards [hs,hvz] with w hw hvw
  rw [hvw,hw]

end DukePrimeDegree

end

end OAI
