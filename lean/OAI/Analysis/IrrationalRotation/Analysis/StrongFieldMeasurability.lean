import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

namespace OAI

namespace Invariant233.StrongField

open MeasureTheory Filter
open scoped Topology

variable {X ι H F : Type*} [MeasurableSpace X] [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem stronglyMeasurable_apply_of_columns
    (b : HilbertBasis ι ℂ H) (A : X → H →L[ℂ] F)
    (hA : ∀ i, StronglyMeasurable fun x => A x (b i))
    {v : X → H} (hv : StronglyMeasurable v) :
    StronglyMeasurable fun x => A x (v x) := by
  classical
  let approximant : Finset ι → X → F := fun s x =>
    ∑ i ∈ s, b.repr (v x) i • A x (b i)
  have hm (s : Finset ι) : StronglyMeasurable (approximant s) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    have hc : StronglyMeasurable fun x => b.repr (v x) i := by
      simp only [b.repr_apply_apply]
      exact (innerSL ℂ (b i)).continuous.comp_stronglyMeasurable hv
    exact hc.smul (hA i)
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ι)) hm
  apply tendsto_pi_nhds.mpr
  intro x
  have h := (A x).hasSum (b.hasSum_repr (v x))
  simpa only [HasSum, SummationFilter.unconditional_filter, approximant, map_smul] using h

theorem stronglyMeasurable_apply_const_of_columns
    (b : HilbertBasis ι ℂ H) (A : X → H →L[ℂ] F)
    (hA : ∀ i, StronglyMeasurable fun x => A x (b i)) (v : H) :
    StronglyMeasurable fun x => A x v :=
  stronglyMeasurable_apply_of_columns b A hA stronglyMeasurable_const

theorem aestronglyMeasurable_apply_of_columns
    (b : HilbertBasis ι ℂ H) (A : X → H →L[ℂ] F) {μ : Measure X}
    (hA : ∀ i, AEStronglyMeasurable (fun x => A x (b i)) μ)
    {v : X → H} (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun x => A x (v x)) μ := by
  classical
  let approximant : Finset ι → X → F := fun s x =>
    ∑ i ∈ s, b.repr (v x) i • A x (b i)
  have hm (s : Finset ι) : AEStronglyMeasurable (approximant s) μ := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro i hi
    have hc : AEStronglyMeasurable (fun x => b.repr (v x) i) μ := by
      simp only [b.repr_apply_apply]
      exact (innerSL ℂ (b i)).continuous.comp_aestronglyMeasurable hv
    exact hc.smul (hA i)
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι)) hm
  apply Filter.Eventually.of_forall
  intro x
  have h := (A x).hasSum (b.hasSum_repr (v x))
  simpa only [HasSum, SummationFilter.unconditional_filter, approximant, map_smul] using h

theorem stronglyMeasurable_of_coordinates (b : HilbertBasis ι ℂ H)
    {v : X → H} (hv : ∀ i, StronglyMeasurable fun x => b.repr (v x) i) :
    StronglyMeasurable v := by
  classical
  let approximant : Finset ι → X → H := fun s x =>
    ∑ i ∈ s, b.repr (v x) i • b i
  have hm (s : Finset ι) : StronglyMeasurable (approximant s) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    exact (hv i).smul_const (b i)
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ι)) hm
  apply tendsto_pi_nhds.mpr
  intro x
  simpa only [HasSum, SummationFilter.unconditional_filter, approximant] using b.hasSum_repr (v x)

theorem stronglyMeasurable_adjoint_apply_of_columns [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (A : X → H →L[ℂ] H)
    (hA : ∀ i, StronglyMeasurable fun x => A x (b i)) (v : H) :
    StronglyMeasurable fun x => (A x).adjoint v := by
  apply stronglyMeasurable_of_coordinates b
  intro i
  simp only [b.repr_apply_apply, ContinuousLinearMap.adjoint_inner_right]
  exact (continuous_id.inner continuous_const).comp_stronglyMeasurable (hA i)

theorem stronglyMeasurable_comp_apply_of_columns
    (b : HilbertBasis ι ℂ H) (A B : X → H →L[ℂ] H)
    (hA : ∀ i, StronglyMeasurable fun x => A x (b i))
    (hB : ∀ i, StronglyMeasurable fun x => B x (b i)) (v : H) :
    StronglyMeasurable fun x => (A x).comp (B x) v := by
  exact stronglyMeasurable_apply_of_columns b A hA
    (stronglyMeasurable_apply_const_of_columns b B hB v)

end Invariant233.StrongField

end OAI
