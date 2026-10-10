import OAI.Analysis.CircleDomains.Topology.RoundDiskStokes
import OAI.Analysis.CircleDomains.Selection.RoundHoleOffsets

namespace OAI

/-! Removal of the positive offsets in the finite Stokes estimate. The
hypothesis records arbitrarily close collar oscillation bounds, allowing
upper semicontinuous boundary oscillation rather than assuming a limit. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators

noncomputable section
namespace CircleDomainRigidity

 theorem zero_offset_stokes_bound
    {I : Type*} [Fintype I] (r A : I → ℝ)
    (hA : ∀ i, 0 ≤ A i) (outer E : ℝ)
    (hbound : ∀ ε > 0, ∃ ρ > 0, ρ ≤ ε ∧
      |outer| ≤ E + ε + ρ + ∑ i, 2 * Real.pi * (r i + ρ) * (A i + ε)) :
    |outer| ≤ E + ∑ i, 2 * Real.pi * r i * A i := by
  let f : ℝ → ℝ := fun ε => E + ε + ε + ∑ i, 2 * Real.pi * (r i + ε) * (A i + ε)
  have hf : Continuous f := by dsimp only [f]; fun_prop
  have hlim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (E + ∑ i, 2 * Real.pi * r i * A i)) := by
    simpa only [f, add_zero] using
      (hf.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨ρ, hρ, hρε, hI⟩ := hbound ε hε
  refine hI.trans ?_
  apply add_le_add
  · linarith
  · apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hρε) (by positivity))
      (add_nonneg (hA i) hε.le)

end CircleDomainRigidity

end

end OAI
