import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# A common terminal index for finitely many detectors

This finite-filter argument chooses one actual index at which all scalar
prediction detectors and the total displacement bound hold.  Its applications
supply the scalar limits by evaluating continuous linear functionals on the
actual weak prediction limits, and supply displacement convergence for the
actual finite collection of node maps.
-/

noncomputable section

open Filter
open scoped Topology

namespace ReflexiveFixedPoints

/-- Finitely many detector limits and one displacement limit can be met at the
same index.  No uniform lower bound on the positive detector errors is needed. -/
theorem common_terminal_of_tendsto
    {I J : Type*} [Finite I] {l : Filter J} [NeBot l]
    (e a : I → ℝ) (g : I → J → ℝ) (D : J → ℝ) (M : ℝ)
    (he : ∀ i, 0 < e i)
    (ha : ∀ i, 1 - e i ≤ a i)
    (hg : ∀ i, Tendsto (g i) l (𝓝 (a i)))
    (hD : Tendsto D l (𝓝 0)) (hM : 0 < M) :
    ∃ j, (∀ i, 1 - 2 * e i ≤ g i j) ∧ D j ≤ M := by
  have hdet : ∀ᶠ j in l, ∀ i, 1 - 2 * e i ≤ g i j := by
    apply Filter.eventually_all.mpr
    intro i
    have hgap : 1 - 2 * e i < a i := by
      have := he i
      have := ha i
      linarith
    exact ((hg i).eventually_const_lt hgap).mono fun _ hj => le_of_lt hj
  have hdisp : ∀ᶠ j in l, D j ≤ M :=
    (hD.eventually_lt_const hM).mono fun _ hj => le_of_lt hj
  exact (hdet.and hdisp).exists

/-- The displacement may converge in a larger filter, in particular the
cofinite filter contained in a fixed free ultrafilter. -/
theorem common_terminal_of_tendsto_mono
    {I J : Type*} [Finite I] {l l' : Filter J} [NeBot l]
    (hll' : l ≤ l')
    (e a : I → ℝ) (g : I → J → ℝ) (D : J → ℝ) (M : ℝ)
    (he : ∀ i, 0 < e i)
    (ha : ∀ i, 1 - e i ≤ a i)
    (hg : ∀ i, Tendsto (g i) l (𝓝 (a i)))
    (hD : Tendsto D l' (𝓝 0)) (hM : 0 < M) :
    ∃ j, (∀ i, 1 - 2 * e i ≤ g i j) ∧ D j ≤ M :=
  common_terminal_of_tendsto e a g D M he ha hg (hD.mono_left hll') hM

end ReflexiveFixedPoints

end

end OAI
