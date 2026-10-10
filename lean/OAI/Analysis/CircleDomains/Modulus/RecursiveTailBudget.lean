import OAI.Analysis.CircleDomains.Selection.RecursiveTestHistory
import OAI.Analysis.CircleDomains.Probability.SummableRecursiveBudget

namespace OAI

/-! Every finite tail spends less than one quarter of a previously saved
tolerance. This controls both coordinates of each saved barrier. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "τ" => savedTolerance hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem tail_budget_le_saved {s k : ℕ} (hsk : s+1 ≤ k) (n : ℕ) :
    (∑ j ∈ Finset.range n, recursiveTestBudget ε (k+j) (states (k+j)).tolerances) ≤ τ s/4 := by
  have hτ := savedTolerance_pos hsupply hsard hsch hG hinf hTD ha hBa hε T s
  have hsum : (∑ j ∈ Finset.Ico k (k+n), recursiveTestBudget ε j (states j).tolerances) ≤ τ s/4 := by
    calc
      _ ≤ ∑ j ∈ Finset.Ico k (k+n), (1/2 : ℝ)^(j+3)*τ s := by
        apply Finset.sum_le_sum
        intro j hj
        exact later_budget_le_saved hsupply hsard hsch hG hinf hTD ha hBa hε T
          (hsk.trans (Finset.mem_Ico.mp hj).1)
      _ ≤ ∑' j : ℕ, (1/2 : ℝ)^(j+3)*τ s :=
        (summable_geometric_test_budget (τ s)).sum_le_tsum _ (fun _ _ => by positivity)
      _ = τ s/4 := tsum_geometric_test_budget _
  simpa only [Finset.sum_Ico_eq_sum_range,Nat.add_sub_cancel_left] using hsum

end AppendingSequence
end CircleDomainRigidity

end

end OAI
