import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperContextTransport
import OAI.Combinatorics.ContingencyTables.Transport.IntegerChildLogConcavity

namespace OAI

/-! # Child-mass minimum for the actual first-paper context

Ordinary unexposed pairs are summed with their actual balances before
applying the proved two-coordinate removal inequality and its hard limit.
-/

namespace ContingencyTables.FirstPaperContextTransport

open scoped BigOperators Classical Topology
open LargePairEnumeration IntegerWeightedTransport BalancedFamily BalancedBox

universe u

variable {I J C : Type u} [Fintype I] [Fintype J] [Fintype C] [DecidableEq C]

theorem context_child_minimum (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ mC : C → ℕ) (U : ℕ) (hprefix : InBox mC σ)
    (hlarge : ∀ i j, small i j=false → 2 ≤ B i j)
    (hlower : ∀ w ∈ Ms, 2 ≤ w)
    (a j b : ℕ) (haj : a ≤ j) (hjb : j ≤ b) (hbU : b ≤ U) :
    min (eliminate Ms (contextHard small B r c L Ms e σ) (childProfile U a))
      (eliminate Ms (contextHard small B r c L Ms e σ) (childProfile U b)) ≤
      eliminate Ms (contextHard small B r c L Ms e σ) (childProfile U j) := by
  apply child_minimum_limit
    (fun α => eliminate Ms (contextSoft small B r c L Ms e σ α)) _ U
    (eliminate_tendsto Ms _ _ (contextSoft_tendsto small B r c L Ms e σ)) _ a j b haj hjb hbU
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with α hα
  have hp := contextSoft_slices small B r c L Ms e σ mC (fun _ => U) U hprefix α hα hlarge
  exact eliminate_slices Ms (fun _ => U) U _ hlower hp.1 hp.2

end ContingencyTables.FirstPaperContextTransport

end OAI
