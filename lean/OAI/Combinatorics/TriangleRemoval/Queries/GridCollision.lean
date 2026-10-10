import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.TriangleHypergraph
import OAI.Combinatorics.TriangleRemoval.Stability.GridCavityError

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

section Continuum
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem gridAnswer_tendsto_terminal (H : τ → Finset ι) (focus : Finset ι)
    (parent : Option τ) :
    Tendsto (fun n : ℕ => gridAnswerProbability H (n + 1) (n + 1) (n + 1) focus parent)
      atTop (𝓝 (∏ e ∈ focus, cavityLimit H e parent 1)) := by
  have hh := tendsto_finsetProd focus (fun e _ => gridMessage_tendsto_terminal H e parent)
  convert hh using 1
  funext n
  exact gridAnswerProbability_factor H (n + 1) (n + 1) (n + 1) focus parent

noncomputable def gridCollision (H : τ → Finset ι) (focus : Finset ι)
    (parent : Option τ) (n : ℕ) : ℝ :=
  trueProbability ((ExposureTree.freshRecorded (gridPriorities (n + 1))
    (gridQueryDepth H (n + 1) (n + 1) (n + 1) focus parent) ∅).map Prod.snd)

noncomputable def collisionCost (H : τ → Finset ι) (focus : Finset ι)
    (parent : Option τ) : ℝ :=
  Filter.liminf (gridCollision H focus parent) atTop

omit [Fintype ι] in
theorem gridCollision_mem_unit (H : τ → Finset ι) (focus : Finset ι)
    (parent : Option τ) (n : ℕ) : gridCollision H focus parent n ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨trueProbability_nonneg _, trueProbability_le_one _⟩

omit [Fintype ι] in
theorem collisionCost_mem_unit (H : τ → Finset ι) (focus : Finset ι)
    (parent : Option τ) : collisionCost H focus parent ∈ Set.Icc (0 : ℝ) 1 := by
  have hlow : atTop.IsBoundedUnder (· ≥ ·) (gridCollision H focus parent) :=
    Filter.isBoundedUnder_of ⟨0, fun n => (gridCollision_mem_unit H focus parent n).1⟩
  have hupp : atTop.IsBoundedUnder (· ≤ ·) (gridCollision H focus parent) :=
    Filter.isBoundedUnder_of ⟨1, fun n => (gridCollision_mem_unit H focus parent n).2⟩
  constructor
  · exact le_liminf_of_le hupp.isCobounded_flip
      (Filter.Eventually.of_forall (fun n => (gridCollision_mem_unit H focus parent n).1))
  · apply liminf_le_of_le hlow
    intro b hb
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (gridCollision_mem_unit H focus parent n).2

end Continuum

theorem graph_cavity_error {n : ℕ} (G focus : Graph n) (hf : focus ⊆ G) :
    |focusSurvival G focus - ∏ e ∈ focus, cavityLimit (triangleHypergraph G) e none 1| ≤
      collisionCost (triangleHypergraph G) focus none := by
  let H := triangleHypergraph G
  let C : ℝ := 2 * (Fintype.card (Finset (Fin n)) : ℝ) ^ 2
  let a : ℕ → ℝ := fun k =>
    |focusSurvival G focus - gridAnswerProbability H (k + 1) (k + 1) (k + 1) focus none| -
      C / (k + 1 : ℕ)
  have hden : Tendsto (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 0))
  have ha : Tendsto a atTop
      (𝓝 |focusSurvival G focus - ∏ e ∈ focus, cavityLimit H e none 1|) := by
    have hh := (((tendsto_const_nhds (x := focusSurvival G focus)).sub (gridAnswer_tendsto_terminal H focus none)).abs).sub
      ((tendsto_const_nhds (x := C)).mul hden)
    simpa only [a, mul_zero, sub_zero, div_eq_mul_inv, one_mul] using hh
  have he : ∀ᶠ k in atTop, a k ≤ gridCollision H focus none k := by
    apply Filter.Eventually.of_forall
    intro k
    have hh := graph_grid_exposure_error G focus hf (k + 1)
    dsimp only [a, C, H, gridCollision]
    linarith
  have hupp : atTop.IsBoundedUnder (· ≤ ·) (gridCollision H focus none) :=
    Filter.isBoundedUnder_of ⟨1, fun k => (gridCollision_mem_unit H focus none k).2⟩
  have hh := liminf_le_liminf he ha.isBoundedUnder_ge hupp.isCobounded_flip
  rw [ha.liminf_eq] at hh
  exact hh

end SharpTerminalLeave

end

end OAI
