import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.Basic

namespace OAI

/-!
# Vanishing of uniformly bounded functionals on a closed span

Convergence on the generators extends first by linearity to their span,
then by an explicit epsilon estimate to its norm closure. Summable budgets
also vanish along any injective sequence of their actual indices.
-/

open Filter Topology

namespace ReflexiveFixedPoints

/-- A sequence of functionals of norm at most one that tends to zero on a
set of generators tends to zero at each point of their closed linear span. -/
theorem tendsto_zero_of_mem_closedSpan
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ℕ → X →L[ℝ] ℝ) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    {s : Set X}
    (hs : ∀ x ∈ s, Tendsto (fun n => φ n x) atTop (𝓝 0))
    {x : X} (hx : x ∈ (Submodule.span ℝ s).topologicalClosure) :
    Tendsto (fun n => φ n x) atTop (𝓝 0) := by
  have hspan : ∀ y ∈ Submodule.span ℝ s,
      Tendsto (fun n => φ n y) atTop (𝓝 0) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hs y hy
    | zero =>
        simpa only [map_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    | add y z _ _ hy hz =>
        simpa only [map_add, add_zero] using hy.add hz
    | smul a y _ hy =>
        simpa only [map_smul, smul_zero] using hy.const_smul a
  change x ∈ closure (Submodule.span ℝ s : Set X) at hx
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hspan y hy) (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hdist : dist (φ n x) (φ n y) ≤ dist x y := by
    calc
      dist (φ n x) (φ n y) ≤ ‖φ n‖ * dist x y := (φ n).dist_le_opNorm x y
      _ ≤ 1 * dist x y := mul_le_mul_of_nonneg_right (hφ n) dist_nonneg
      _ = dist x y := one_mul _
  calc
    dist (φ n x) 0 ≤ dist (φ n x) (φ n y) + dist (φ n y) 0 := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hdist.trans_lt hxy) (hN n hn)
    _ = ε := add_halves ε

/-- Summable budgets tend to zero along any injective sequence of indices. -/
theorem summable_budget_tendsto {I : Type*}
    (e : I → ℝ) (he : Summable e)
    (b : ℕ → I) (hb : Function.Injective b) :
    Tendsto (fun n => e (b n)) atTop (𝓝 0) :=
  (he.comp_injective hb).tendsto_atTop_zero

end ReflexiveFixedPoints

end OAI
