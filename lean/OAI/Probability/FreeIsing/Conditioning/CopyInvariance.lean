import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace Problem367

variable {W X Y : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Y]

lemma map_compProd_prodMap (mu : Measure W) [SFinite mu]
    (kappa : Kernel W X) [IsSFiniteKernel kappa]
    (T : W ≃ᵐ W) {S : X → Y} (hS : Measurable S) :
    (mu ⊗ₘ kappa).map (Prod.map T S) =
      mu.map T ⊗ₘ (kappa.comap T.symm T.symm.measurable).map S := by
  ext A hA
  rw [Measure.map_apply (T.measurable.prodMap hS) hA,
    Measure.compProd_apply ((T.measurable.prodMap hS) hA),
    Measure.compProd_apply hA,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hA) T.measurable]
  apply lintegral_congr
  intro w
  rw [Kernel.map_apply' _ hS _ (measurable_prodMk_left hA), Kernel.comap_apply]
  simp only [MeasurableEquiv.symm_apply_apply]
  rfl

lemma kernel_ae_equivariant_of_joint_invariant
    (mu : Measure W) [IsFiniteMeasure mu]
    (kappa : Kernel W X) [IsFiniteKernel kappa]
    [MeasurableSpace.CountableOrCountablyGenerated W X]
    (T : W ≃ᵐ W) {S : X → X} (hS : Measurable S)
    (hT : MeasurePreserving T mu mu)
    (hjoint : (mu ⊗ₘ kappa).map (Prod.map T S) = mu ⊗ₘ kappa) :
    ∀ᵐ w ∂mu, kappa (T w) = (kappa w).map S := by
  have heq : (kappa.comap T.symm T.symm.measurable).map S =ᵐ[mu] kappa := by
    apply Kernel.ae_eq_of_compProd_eq
    have h := hjoint
    rw [map_compProd_prodMap mu kappa T hS, hT.map_eq] at h
    exact h
  have htrans := hT.quasiMeasurePreserving.ae heq
  filter_upwards [htrans] with w hw
  simpa only [Kernel.map_apply _ hS, Kernel.comap_apply,
    MeasurableEquiv.symm_apply_apply] using hw.symm

lemma joint_invariant_of_kernel_ae_equivariant
    (mu : Measure W) [SFinite mu]
    (kappa : Kernel W X) [IsSFiniteKernel kappa]
    (T : W ≃ᵐ W) {S : X → X} (hS : Measurable S)
    (hT : MeasurePreserving T mu mu)
    (hkappa : ∀ᵐ w ∂mu, kappa (T w) = (kappa w).map S) :
    (mu ⊗ₘ kappa).map (Prod.map T S) = mu ⊗ₘ kappa := by
  rw [map_compProd_prodMap mu kappa T hS, hT.map_eq]
  apply Measure.compProd_congr
  have htrans := hT.symm.quasiMeasurePreserving.ae hkappa
  filter_upwards [htrans] with w hw
  simpa only [Kernel.map_apply _ hS, Kernel.comap_apply,
    MeasurableEquiv.apply_symm_apply] using hw.symm

lemma conditionalCopies_invariant
    (mu : Measure W) [IsFiniteMeasure mu]
    (kappa : Kernel W X) [IsFiniteKernel kappa]
    [MeasurableSpace.CountableOrCountablyGenerated W X]
    (T : W ≃ᵐ W) {S : X → X} (hS : Measurable S)
    (hT : MeasurePreserving T mu mu)
    (hjoint : (mu ⊗ₘ kappa).map (Prod.map T S) = mu ⊗ₘ kappa) :
    (mu ⊗ₘ (kappa ×ₖ kappa)).map (Prod.map T (Prod.map S S)) =
      mu ⊗ₘ (kappa ×ₖ kappa) := by
  apply joint_invariant_of_kernel_ae_equivariant mu (kappa ×ₖ kappa) T
    (hS.prodMap hS) hT
  filter_upwards [kernel_ae_equivariant_of_joint_invariant mu kappa T hS hT hjoint]
    with w hw
  simp only [Kernel.prod_apply, hw]
  exact Measure.map_prod_map (kappa w) (kappa w) hS hS

end Problem367

end

end OAI
