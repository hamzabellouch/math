import OAI.NumberTheory.DukePrimeDegree.Geometry.FiniteKernelEquality

namespace OAI

/-! # Exchanged conditional measures at almost every original sample -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {S : Type*} [MeasurableSpace S]

def nextConjugatedKernel (d : ℕ) (q : InitialRootStep (d+1))
    (κ : Kernel S (positiveRootGeneratedGroup (q.remaining.erase q.root))) [IsSFiniteKernel κ] :
    Kernel (S × ℝ) (positiveRootGeneratedGroup (q.remaining.erase q.root)) where
  toFun z := (κ z.1).map (q.nextConjugation d z.2)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro U hU
    have H := Kernel.measurable_kernel_prodMk_left (κ := Kernel.prodMkRight ℝ κ)
      (((q.continuous_conjugationSkew d).snd.measurable.comp
        (measurable_fst.snd.prodMk measurable_snd)) hU)
    convert H using 1
    funext z
    exact Measure.map_apply (q.continuous_nextConjugation d z.2).measurable hU

instance nextConjugatedKernel_markov (d : ℕ) (q : InitialRootStep (d+1))
    (κ : Kernel S (positiveRootGeneratedGroup (q.remaining.erase q.root))) [IsMarkovKernel κ] :
    IsMarkovKernel (q.nextConjugatedKernel d κ) where
  isProbabilityMeasure z := by
    change IsProbabilityMeasure ((κ z.1).map (q.nextConjugation d z.2))
    apply (Measure.isProbabilityMeasure_map_iff
      (q.continuous_nextConjugation d z.2).measurable.aemeasurable).mpr
    infer_instance

theorem ae_prefixRootExchange_conditional_at_sample (d : ℕ) (q : InitialRootStep (d+1))
    (ρ : Measure (S × (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)))
    [IsFiniteMeasure ρ]
    (hprod : ∀ᵐ s ∂ρ.fst,
      ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd) :
    ∀ᵐ z ∂ρ, (ρ.map (q.prefixRootExchange d)).condKernel (z.1,z.2.2) =
      ((ρ.condKernel z.1).fst).map (q.nextConjugation d z.2.2) := by
  let f : S × (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) → S × ℝ :=
    fun z => (z.1,z.2.2)
  have hf : Measurable f := measurable_fst.prodMk measurable_snd.snd
  let κ := q.nextConjugatedKernel d ρ.condKernel.fst
  have H : ∀ᵐ z ∂ρ,
      (ρ.map (q.prefixRootExchange d)).condKernel (f z) = κ (f z) := by
    apply finiteKernels_ae_eq_of_apply
      ((ρ.map (q.prefixRootExchange d)).condKernel.comap f hf) (κ.comap f hf) ρ
    intro U hU
    change ∀ᵐ z ∂ρ, (ρ.map (q.prefixRootExchange d)).condKernel (f z) U = κ (f z) U
    have hm : MeasurableSet {z | (ρ.map (q.prefixRootExchange d)).condKernel (f z) U = κ (f z) U} :=
      measurableSet_eq_fun
        (((ρ.map (q.prefixRootExchange d)).condKernel.measurable_coe hU).comp hf)
        ((κ.measurable_coe hU).comp hf)
    have H' : ∀ᵐ z ∂ρ.fst ⊗ₘ ρ.condKernel,
        (ρ.map (q.prefixRootExchange d)).condKernel (f z) U = κ (f z) U := by
      apply Measure.ae_compProd_of_ae_ae hm
      filter_upwards [q.ae_prefixRootExchange_conditional d ρ hprod] with s hs
      exact ae_of_ae_map measurable_snd.aemeasurable
        (hs.mono fun t ht => congrArg (fun ν => ν U) ht)
    simpa only [Measure.disintegrate] using H'
  exact H

end InitialRootStep
end DukePrimeDegree

end

end OAI
