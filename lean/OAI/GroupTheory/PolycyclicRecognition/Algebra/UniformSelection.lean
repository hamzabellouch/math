import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace OAI

/-! # Uniform estimates from arbitrary parameter selections -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- To prove uniform convergence to a constant, it suffices to control every
choice of one parameter at each index. No topology on the parameter set is
needed. This lets a common word-coefficient envelope control whole families. -/
theorem tendstoUniformly_const_of_all_selections
    {ι Z V : Type*} [PseudoMetricSpace V] {l : Filter ι}
    (F : ι → Z → V) (v : V)
    (h : ∀ z : ι → Z, Tendsto (fun i => F i (z i)) l (𝓝 v)) :
    TendstoUniformly F (fun _ => v) l := by
  classical
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  by_cases hz : Nonempty Z
  · let := hz
    let z : ι → Z := fun i => if hi : ∃ z, ¬dist v (F i z) < ε then
      Classical.choose hi else Classical.choice hz
    have hb (i : ι) (hi : ∃ z, ¬dist v (F i z) < ε) :
        ¬dist v (F i (z i)) < ε := by
      simpa only [z, dite_eq_left hi] using Classical.choose_spec hi
    have hp := (Metric.tendsto_nhds.mp (h z)) ε hε
    filter_upwards [hp] with i hi
    intro y
    by_contra hy
    exact hb i ⟨y, hy⟩ (by simpa only [dist_comm] using hi)
  · exact Eventually.of_forall (fun _ z => False.elim (hz ⟨z⟩))

/-- Uniform convergence to a constant permits a different parameter at
every index. -/
theorem tendsto_selection_of_tendstoUniformly_const
    {ι Z V : Type*} [PseudoMetricSpace V] {l : Filter ι}
    {F : ι → Z → V} {v : V}
    (h : TendstoUniformly F (fun _ => v) l) (z : ι → Z) :
    Tendsto (fun i => F i (z i)) l (𝓝 v) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp h) ε hε] with i hi
  simpa only [dist_comm] using hi (z i)

end PolycyclicRecognition

end OAI
