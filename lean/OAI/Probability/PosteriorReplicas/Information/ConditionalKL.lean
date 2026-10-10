import OAI.Probability.PosteriorReplicas.Information.KLTools
import OAI.Probability.PosteriorReplicas.Model

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

section Conditional
variable {Z X Y : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
  (μ : Measure Z) [IsFiniteMeasure μ]
  (κ : Kernel Z (X × Y)) (η : Kernel Z X) (ρ : Kernel Z Y)
  [IsMarkovKernel κ] [IsMarkovKernel η] [IsMarkovKernel ρ]

lemma klDiv_kernel_prod_decomposition :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (η ×ₖ ρ)) =
      klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) +
      klDiv (μ ⊗ₘ κ.fst) (μ ⊗ₘ η) + klDiv (μ ⊗ₘ κ.snd) (μ ⊗ₘ ρ) := by
  simp_rw [klDiv_compProd_kernel]
  calc
    _ = ∫⁻ z, (klDiv (κ z) ((κ.fst ×ₖ κ.snd) z) +
        klDiv (κ.fst z) (η z)) + klDiv (κ.snd z) (ρ z) ∂μ := by
      apply lintegral_congr
      intro z
      have h := klDiv_prod_decomposition (κ z) (η z) (ρ z)
      simpa only [Kernel.prod_apply, Kernel.fst_apply, Kernel.snd_apply,
        Measure.fst, Measure.snd, add_assoc, add_comm, add_left_comm] using h
    _ = _ := by
      rw [lintegral_add_aux (by
          exact ((measurable_kernel_klDiv κ (κ.fst ×ₖ κ.snd)).add
            (measurable_kernel_klDiv κ.fst η)))
          (measurable_kernel_klDiv κ.snd ρ),
        lintegral_add_aux (measurable_kernel_klDiv κ (κ.fst ×ₖ κ.snd))
          (measurable_kernel_klDiv κ.fst η)]

end Conditional

lemma cmi_eq_kernel_integral {Z X Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    (q : Measure (Z × (X × Y))) [IsFiniteMeasure q] :
    cmi q = ∫⁻ z, klDiv (q.condKernel z)
      ((q.condKernel z).fst.prod (q.condKernel z).snd) ∂q.fst := by
  unfold cmi
  conv_lhs => lhs; rw [← Measure.disintegrate q q.condKernel]
  rw [klDiv_compProd_kernel]
  simp only [Kernel.prod_apply, Kernel.fst_apply, Kernel.snd_apply, Measure.fst, Measure.snd]

lemma klDiv_conditional_chain {Z X Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    (q : Measure (Z × (X × Y))) [IsProbabilityMeasure q]
    (ν : Measure Y) [IsProbabilityMeasure ν] :
    klDiv q (q.fst ⊗ₘ (q.condKernel.fst ×ₖ Kernel.const Z ν)) =
      cmi q + klDiv (q.map (fun z => (z.1, z.2.2))) (q.fst.prod ν) := by
  have h := klDiv_kernel_prod_decomposition q.fst q.condKernel q.condKernel.fst
    (Kernel.const Z ν)
  rw [Measure.disintegrate q q.condKernel, klDiv_self, add_zero, Measure.compProd_const] at h
  rw [Kernel.snd_eq, Measure.compProd_map measurable_snd,
    Measure.disintegrate q q.condKernel] at h
  have hm : (Prod.map id Prod.snd : Z × (X × Y) → Z × Y) = (fun z => (z.1,z.2.2)) := by
    funext z
    rfl
  rw [hm] at h
  simpa only [cmi, Kernel.snd_eq] using h

end PosteriorReplicas
end

end OAI
