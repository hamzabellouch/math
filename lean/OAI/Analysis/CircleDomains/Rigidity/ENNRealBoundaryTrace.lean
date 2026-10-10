import OAI.Analysis.CircleDomains.Rigidity.BoundaryTrace
import OAI.Analysis.CircleDomains.Selection.ShrinkingJumpTolls

namespace OAI

/-! Pointwise trace convergence and the countable exceptional set for the
ENNReal dust budgets used by the constructed chain potential. -/

open Set Filter
open scoped Topology ENNReal

namespace CircleDomainRigidity

theorem countable_square_toll_support {X : Type*} {m : X → ℝ≥0∞}
    (hm : (∑' x, m x ^ 2) ≠ ∞) : {x | m x ≠ 0}.Countable := by
  simpa only [Function.support, ne_eq, sq_eq_zero_iff] using
    (Summable.countable_support_ennreal hm)

theorem boundaryTrace_of_ennreal_budget
    {X : Type*} [TopologicalSpace X] {G B : Set X} {u : X → ℝ} {m : X → ℝ≥0∞}
    (hu : ∀x ∈ G, u x ∈ Icc 0 1) (hB : B ⊆ closure G)
    (hm : (∑' x, m x ^ 2) ≠ ∞)
    (hband : ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[G] s) - liminf u (𝓝[G] s)) ≤ 4 * m s) :
    {x | m x ≠ 0}.Countable ∧ ∀s ∈ B, m s = 0 →
      Tendsto u (𝓝[G] s) (𝓝 (realBoundaryTrace G u s)) := by
  refine ⟨countable_square_toll_support hm, ?_⟩
  intro s hs hzero
  apply tendsto_boundaryTrace_of_zero_band (M := 1)
  · intro x hx
    rw [abs_of_nonneg (hu x hx).1]
    exact (hu x hx).2
  · exact hB hs
  · have h := hband s hs
    rw [hzero, mul_zero] at h
    exact ENNReal.ofReal_eq_zero.mp (le_antisymm h bot_le)

end CircleDomainRigidity

end OAI
