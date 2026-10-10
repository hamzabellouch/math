import OAI.NumberTheory.DukePrimeDegree.Geometry.RootOrderCoordinates
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingRootProductBoxes

namespace OAI

/-! # Conditional kernels under the actual noncommuting coordinate exchange -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

theorem rootOrderCoordinates_conditional (d : ℕ) (q : InitialRootStep (d+1))
    (ρ : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ))
    [IsFiniteMeasure ρ] :
    ∀ᵐ t ∂ρ.snd,
      (ρ.map (q.rootOrderCoordinates d)).condKernel t =
        ((ρ.map Prod.swap).condKernel t).map (q.nextConjugation d t) := by
  let σ := ρ.map Prod.swap
  have h := conditional_map_fibers σ (MeasurableEquiv.refl ℝ)
    (fun z => q.nextConjugation d z.1 z.2) (q.continuous_conjugationSkew d).snd.measurable
  have hm : σ.map (fun z => (z.1,q.nextConjugation d z.1 z.2)) =
      ρ.map (q.rootOrderCoordinates d) := by
    dsimp only [σ]
    rw [Measure.map_map (q.continuous_conjugationSkew d).measurable measurable_swap]
    rfl
  have hf : σ.fst = ρ.snd := by
    dsimp only [σ]
    exact Measure.fst_map_swap
  simpa only [hf,hm,MeasurableEquiv.refl_apply,σ] using h

theorem rootOrderCoordinates_conditional_of_product (d : ℕ) (q : InitialRootStep (d+1))
    (ρ : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ))
    [IsProbabilityMeasure ρ] (hprod : ρ = ρ.fst.prod ρ.snd) :
    ∀ᵐ t ∂ρ.snd,
      (ρ.map (q.rootOrderCoordinates d)).condKernel t = ρ.fst.map (q.nextConjugation d t) := by
  have he : ρ.map Prod.swap = ρ.snd.prod ρ.fst := by
    conv_lhs => rw [hprod]
    exact Measure.prod_swap
  have hdis : ρ.map Prod.swap = (ρ.map Prod.swap).fst ⊗ₘ Kernel.const ℝ ρ.fst := by
    rw [he,Measure.fst_prod,Measure.compProd_const]
  have hc := eq_condKernel_of_measure_eq_compProd (Kernel.const ℝ ρ.fst) hdis
  rw [Measure.fst_map_swap] at hc
  filter_upwards [q.rootOrderCoordinates_conditional d ρ,hc] with t ht hc
  rw [ht,←hc,Kernel.const_apply]

end InitialRootStep
end DukePrimeDegree

end

end OAI
