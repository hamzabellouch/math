import OAI.Analysis.CoulombTransport.Model

namespace OAI

universe uIndex

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.ComponentPotential

variable {ι : Type uIndex} [Fintype ι]

/-- Glue local potentials on disjoint components, with value zero outside them. -/
def glue (U : ι → Set E3) (u : ι → E3 → ℝ) (x : E3) : ℝ :=
  ∑ i, (U i).indicator (u i) x

theorem glue_eq {U : ι → Set E3} {u : ι → E3 → ℝ}
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j))) {i : ι} {x : E3}
    (hx : x ∈ U i) : glue U u x = u i x := by
  classical
  unfold glue
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro j _ hji
    apply indicator_of_notMem
    intro hxj
    exact Set.disjoint_left.mp (hdisj hji) hxj hx
  · simp

theorem glue_eq_zero {U : ι → Set E3} {u : ι → E3 → ℝ} {x : E3}
    (hx : x ∉ ⋃ i, U i) : glue U u x = 0 := by
  classical
  unfold glue
  apply Finset.sum_eq_zero
  intro i _
  apply indicator_of_notMem
  intro hxi
  exact hx (mem_iUnion.mpr ⟨i, hxi⟩)

/-- Local continuity is sufficient for global Borel measurability of the extension. -/
theorem measurable_glue {U : ι → Set E3} {u : ι → E3 → ℝ}
    (hU : ∀ i, MeasurableSet (U i)) (hu : ∀ i, ContinuousOn (u i) (U i)) :
    Measurable (glue U u) := by
  classical
  unfold glue
  apply Finset.measurable_sum
  intro i _
  change Measurable ((U i).piecewise (u i) (fun _ => 0))
  exact (hu i).measurable_piecewise continuousOn_const (hU i)

/-- Gluing preserves continuity on the open union of pairwise disjoint components. -/
theorem continuousOn_glue {U : ι → Set E3} {u : ι → E3 → ℝ}
    (hU : ∀ i, IsOpen (U i))
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hu : ∀ i, ContinuousOn (u i) (U i)) :
    ContinuousOn (glue U u) (⋃ i, U i) := by
  apply ContinuousOn.iUnion_of_isOpen _ hU
  intro i
  apply (hu i).congr
  intro x hx
  exact glue_eq hdisj hx

/-- A common absolute bound passes to the glued potential, globally if it is nonnegative. -/
theorem abs_glue_le {U : ι → Set E3} {u : ι → E3 → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hu : ∀ i, ∀ x ∈ U i, |u i x| ≤ M) (x : E3) :
    |glue U u x| ≤ M := by
  by_cases hx : x ∈ ⋃ i, U i
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    rw [glue_eq hdisj hxi]
    exact hu i x hxi
  · rw [glue_eq_zero hx, abs_zero]
    exact hM

/-- A bounded glued potential is integrable against every finite marginal. -/
theorem integrable_glue {U : ι → Set E3} {u : ι → E3 → ℝ} {M : ℝ}
    {mu : Measure E3} [IsFiniteMeasure mu]
    (hM : 0 ≤ M) (hU : ∀ i, MeasurableSet (U i))
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hc : ∀ i, ContinuousOn (u i) (U i))
    (hb : ∀ i, ∀ x ∈ U i, |u i x| ≤ M) :
    Integrable (glue U u) mu := by
  apply Integrable.of_bound (measurable_glue hU hc).aestronglyMeasurable M
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using abs_glue_le hM hdisj hb x

end Problem356.ComponentPotential

end

end OAI
