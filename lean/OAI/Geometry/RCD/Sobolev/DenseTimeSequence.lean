import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace OAI

/-! # A countable family dense in every subinterval of a closed time interval -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

theorem exists_dense_time_sequence {δ : ℝ} (hδ : δ ≤ 1) :
    ∃ s : ℕ → ℝ, (∀ i, s i ∈ Icc δ 1) ∧
      ∀ a b : ℝ, δ ≤ a → b ≤ 1 → a < b → ∃ i, a < s i ∧ s i < b := by
  let : Nonempty (Icc δ (1:ℝ)) := ⟨⟨δ,le_rfl,hδ⟩⟩
  let d := TopologicalSpace.denseSeq (Icc δ (1:ℝ))
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq _
  refine ⟨fun i => d i,fun i => (d i).property,?_⟩
  intro a b ha hb hab
  let x : Icc δ (1:ℝ) := ⟨(a+b)/2,by constructor <;> linarith⟩
  obtain ⟨i,hi⟩ := hd.exists_dist_lt x (show 0 < (b-a)/2 by linarith)
  rw [dist_comm] at hi
  change dist (d i : ℝ) ((a+b)/2) < (b-a)/2 at hi
  rw [Real.dist_eq] at hi
  have h := abs_lt.mp hi
  refine ⟨i,?_,?_⟩ <;> linarith

end RegularPointCoordinates

end

end OAI
