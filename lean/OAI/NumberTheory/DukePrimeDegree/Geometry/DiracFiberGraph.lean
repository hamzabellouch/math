import OAI.NumberTheory.DukePrimeDegree.Dynamics.KernelStabilizerMeasurable

namespace OAI

/-! # A common full-measure graph for Dirac fiber conditionals -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree

variable {Z U : Type*} [MeasurableSpace Z] [MeasurableSpace U]
  [StandardBorelSpace U]

def kernelDiracGraph (κ : Kernel Z U) : Set (Z × U) :=
  {z | κ z.1=Measure.dirac z.2}

lemma measurableSet_kernelDiracGraph (κ : Kernel Z U) [IsFiniteKernel κ] :
    MeasurableSet (kernelDiracGraph κ) := by
  have h := measurableSet_finite_kernel_eq (κ.comap Prod.fst measurable_fst)
    (Kernel.deterministic Prod.snd measurable_snd)
  simpa only [kernelDiracGraph,Kernel.comap_apply,Kernel.deterministic_apply] using h

lemma kernelDiracGraph_fiber_unique (κ : Kernel Z U)
    {x y : Z × U} (hx : x ∈ kernelDiracGraph κ)
    (hy : y ∈ kernelDiracGraph κ) (hbase : x.1=y.1) : x.2=y.2 := by
  apply MeasureTheory.injective_dirac
  exact hx.symm.trans ((congrArg κ hbase).trans hy)

theorem exists_full_measure_unique_fiber_graph
    (ρ : Measure (Z × U)) (κ : Kernel Z U) [IsFiniteKernel κ]
    (hκ : ∀ᵐ z ∂ρ, κ z.1=Measure.dirac z.2) :
    ∃ E : Set (Z × U), MeasurableSet E ∧ (∀ᵐ z ∂ρ, z ∈ E) ∧
      ∀ x ∈ E, ∀ y ∈ E, x.1=y.1 → x.2=y.2 :=
  ⟨kernelDiracGraph κ,measurableSet_kernelDiracGraph κ,hκ,
    fun _ hx _ hy he => kernelDiracGraph_fiber_unique κ hx hy he⟩

end DukePrimeDegree

end

end OAI
