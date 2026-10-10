import OAI.Analysis.Nonexpansive.GeneratedMaps
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace OAI

/-!
# One common terminal sequence for all fixed generated maps

The terminal sequence uses zero-based indices. All quantitative estimates
retain the denominator `j+1`.
The sequence is constructed once. Every fixed finite family of generated
maps has total displacement tending to zero along this same sequence.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace ReflexiveFixedPoints

universe u v

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {K : Set X}

def terminalSequence (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T) (x : K) (j : ℕ) : K :=
  resolvent hKclosed hKconvex T hT (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) x

theorem terminalSequence_defect_le (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1) (x : K) (j : ℕ) :
    ‖(T (terminalSequence hKclosed hKconvex T hT x j) : X) -
      (terminalSequence hKclosed hKconvex T hT x j : X)‖ ≤ 1 / ((j : ℝ) + 1) := by
  simpa only [terminalSequence, Nat.cast_add, Nat.cast_one] using
    resolvent_defect_le hKclosed hKconvex T hT hdiam (j + 1)
      (Nat.succ_le_succ (Nat.zero_le j)) x

theorem terminalSequence_defect_tendsto (hKclosed : IsClosed K)
    (hKconvex : Convex ℝ K) (T : K → K) (hT : LipschitzWith 1 T)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1) (x : K) :
    Tendsto (fun j : ℕ =>
      ‖(T (terminalSequence hKclosed hKconvex T hT x j) : X) -
        (terminalSequence hKclosed hKconvex T hT x j : X)‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _)
    (terminalSequence_defect_le hKclosed hKconvex T hT hdiam x)
    tendsto_one_div_add_atTop_nhds_zero_nat

theorem terminalSequence_displacement_le (hKclosed : IsClosed K)
    (hKconvex : Convex ℝ K) (T : K → K) (hT : LipschitzWith 1 T)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    (G : K → K) (c : ℝ) (hc : 0 ≤ c)
    (hG : ∀ a : K, ‖(G a : X) - (a : X)‖ ≤ c * ‖(T a : X) - (a : X)‖)
    (x : K) (j : ℕ) :
    ‖(G (terminalSequence hKclosed hKconvex T hT x j) : X) -
      (terminalSequence hKclosed hKconvex T hT x j : X)‖ ≤ c / ((j : ℝ) + 1) := by
  calc
    _ ≤ c * ‖(T (terminalSequence hKclosed hKconvex T hT x j) : X) -
        (terminalSequence hKclosed hKconvex T hT x j : X)‖ := hG _
    _ ≤ c * (1 / ((j : ℝ) + 1)) := mul_le_mul_of_nonneg_left
      (terminalSequence_defect_le hKclosed hKconvex T hT hdiam x j) hc
    _ = _ := by ring

theorem terminalSequence_generated_displacement
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    {G : K → K} (hG : Generated hKclosed hKconvex T hT G) (x : K) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ j : ℕ,
      ‖(G (terminalSequence hKclosed hKconvex T hT x j) : X) -
        (terminalSequence hKclosed hKconvex T hT x j : X)‖ ≤ c / ((j : ℝ) + 1) := by
  obtain ⟨c, hc, hbound⟩ := generated_displacement hG
  exact ⟨c, hc, terminalSequence_displacement_le hKclosed hKconvex T hT hdiam
    G c hc hbound x⟩

theorem terminalSequence_generated_displacement_tendsto
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    {G : K → K} (hG : Generated hKclosed hKconvex T hT G) (x : K) :
    Tendsto (fun j : ℕ =>
      ‖(G (terminalSequence hKclosed hKconvex T hT x j) : X) -
        (terminalSequence hKclosed hKconvex T hT x j : X)‖) atTop (𝓝 0) := by
  obtain ⟨c, hc, hbound⟩ := generated_displacement hG
  have hlim : Tendsto (fun j : ℕ =>
      c * ‖(T (terminalSequence hKclosed hKconvex T hT x j) : X) -
        (terminalSequence hKclosed hKconvex T hT x j : X)‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (terminalSequence_defect_tendsto hKclosed hKconvex T hT hdiam x)
  exact squeeze_zero (fun _ => norm_nonneg _) (fun j => hbound _) hlim

theorem terminalSequence_finite_displacement_tendsto
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    {ι : Type v} [Fintype ι] (G : ι → K → K)
    (hG : ∀ i, Generated hKclosed hKconvex T hT (G i)) (x : K) :
    Tendsto (fun j : ℕ => ∑ i,
      ‖(G i (terminalSequence hKclosed hKconvex T hT x j) : X) -
        (terminalSequence hKclosed hKconvex T hT x j : X)‖) atTop (𝓝 0) := by
  have hlim := tendsto_finsetSum Finset.univ fun i _ =>
    terminalSequence_generated_displacement_tendsto hKclosed hKconvex T hT hdiam (hG i) x
  simpa only [Finset.sum_const_zero] using hlim

theorem terminalSequence_eventually_finite_displacement_lt
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    {ι : Type v} [Fintype ι] (G : ι → K → K)
    (hG : ∀ i, Generated hKclosed hKconvex T hT (G i))
    (x : K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, (∑ i,
      ‖(G i (terminalSequence hKclosed hKconvex T hT x j) : X) -
        (terminalSequence hKclosed hKconvex T hT x j : X)‖) < ε :=
  Filter.Tendsto.eventually_lt_const hε
    (terminalSequence_finite_displacement_tendsto hKclosed hKconvex T hT hdiam G hG x)

theorem terminalSequence_exists_common_index
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    {ι : Type v} [Fintype ι] (G : ι → K → K)
    (hG : ∀ i, Generated hKclosed hKconvex T hT (G i))
    (x : K) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ j : ℕ, N ≤ j ∧ (∑ i,
      ‖(G i (terminalSequence hKclosed hKconvex T hT x j) : X) -
        (terminalSequence hKclosed hKconvex T hT x j : X)‖) < ε :=
  ((eventually_ge_atTop N).and
    (terminalSequence_eventually_finite_displacement_lt hKclosed hKconvex T hT
      hdiam G hG x hε)).exists

end ReflexiveFixedPoints

end

end OAI
