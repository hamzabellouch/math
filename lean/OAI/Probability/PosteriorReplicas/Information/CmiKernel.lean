import OAI.Probability.PosteriorReplicas.Information.ReplicaInformation

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

section
variable {Z X Y : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
  (μ : Measure Z) [IsFiniteMeasure μ] (κ : Kernel Z (X × Y)) [IsMarkovKernel κ]

lemma cmi_compProd : cmi (μ ⊗ₘ κ) = klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) := by
  unfold cmi
  rw [Measure.fst_compProd]
  congr 1
  apply Measure.compProd_congr
  filter_upwards [condKernel_compProd μ κ] with z hz
  simp only [Kernel.prod_apply, Kernel.fst_apply, Kernel.snd_apply, hz]

lemma cmi_compProd_integral : cmi (μ ⊗ₘ κ) =
    ∫⁻ z, mutualInformation (κ z) ∂μ := by
  rw [cmi_compProd, klDiv_compProd_kernel]
  simp only [mutualInformation, Kernel.prod_apply, Kernel.fst_apply, Kernel.snd_apply,
    Measure.fst, Measure.snd]
end

lemma kernel_compProd_eval {T Z V : Type*}
    [MeasurableSpace T] [MeasurableSpace Z] [MeasurableSpace V]
    (κ : Kernel T Z) [IsSFiniteKernel κ] (η : Kernel (T × Z) V) [IsSFiniteKernel η] (t : T) :
    (κ ⊗ₖ η) t = κ t ⊗ₘ η.comap (fun z => (t,z)) (by fun_prop) := by
  ext s hs
  rw [Kernel.compProd_apply hs, Measure.compProd_apply hs]
  rfl

section Tower
variable {T Z X Y : Type*} [MeasurableSpace T] [MeasurableSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Y]
  [Nonempty X] [Nonempty Y]
  (μ : Measure T) [IsFiniteMeasure μ]
  (κ : Kernel T (Z × (X × Y))) [IsMarkovKernel κ]

lemma cmi_kernel_measurable : Measurable (fun t => cmi (κ t)) := by
  have he (t : T) : cmi (κ t) = klDiv (κ t)
      ((κ.fst ⊗ₖ (κ.condKernel.fst ×ₖ κ.condKernel.snd)) t) := by
    unfold cmi
    congr 1
    rw [kernel_compProd_eval]
    have hf : (κ t).fst = κ.fst t := (Kernel.fst_apply κ t).symm
    rw [hf]
    apply Measure.compProd_congr
    filter_upwards [κ.condKernel_apply_eq_condKernel t] with z hz
    simp only [Kernel.comap_apply, Kernel.prod_apply, Kernel.fst_apply, Kernel.snd_apply]
    rw [hz]
  simp_rw [he]
  exact measurable_kernel_klDiv _ _

lemma cmi_compProd_assoc :
    cmi ((μ ⊗ₘ κ).map (MeasurableEquiv.prodAssoc.symm :
      T × (Z × (X × Y)) ≃ᵐ (T × Z) × (X × Y))) = ∫⁻ t, cmi (κ t) ∂μ := by
  have ha : (μ ⊗ₘ κ).map (MeasurableEquiv.prodAssoc.symm :
      T × (Z × (X × Y)) ≃ᵐ (T × Z) × (X × Y)) =
      (μ ⊗ₘ κ.fst) ⊗ₘ κ.condKernel := by
    conv_lhs => rw [← Kernel.disintegrate κ κ.condKernel]
    exact Measure.compProd_assoc
  simp only [ha]
  rw [cmi_compProd_integral, Measure.lintegral_compProd]
  · apply lintegral_congr
    intro t
    rw [cmi_eq_kernel_integral]
    have hf : (κ t).fst = κ.fst t := (Kernel.fst_apply κ t).symm
    rw [hf]
    apply lintegral_congr_ae
    filter_upwards [κ.condKernel_apply_eq_condKernel t] with z hz
    unfold mutualInformation
    rw [hz]
  · simpa only [mutualInformation, Kernel.prod_apply, Kernel.fst_apply, Kernel.snd_apply,
      Measure.fst, Measure.snd] using
      measurable_kernel_klDiv κ.condKernel (κ.condKernel.fst ×ₖ κ.condKernel.snd)
end Tower

end PosteriorReplicas
end

end OAI
