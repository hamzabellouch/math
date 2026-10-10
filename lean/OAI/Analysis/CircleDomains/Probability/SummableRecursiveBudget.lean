import OAI.Analysis.CircleDomains.Modulus.RecursiveTestBudget
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-! The recursive choices have a summable majorant with an explicit total
and explicit tails, for uniform and gradient convergence. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem summable_geometric_test_budget (ε : ℝ) :
    Summable (fun n : ℕ => (1/2 : ℝ)^(n+3)*ε) := by
  simpa only [pow_add,mul_assoc] using
    summable_geometric_two.mul_right ((1/2 : ℝ)^3*ε)

 theorem tsum_geometric_test_budget (ε : ℝ) :
    (∑' n : ℕ, (1/2 : ℝ)^(n+3)*ε) = ε/4 := by
  simp_rw [pow_add,mul_assoc]
  rw [tsum_mul_right,tsum_geometric_two]
  ring

 theorem summable_recursive_test_budget {ε : ℝ} (hε : 0 < ε)
    (ts : ℕ → List ℝ) (hts : ∀ n t, t ∈ ts n → 0 < t) :
    Summable (fun n => recursiveTestBudget ε n (ts n)) :=
  Summable.of_nonneg_of_le (fun n => (recursiveTestBudget_pos hε n (hts n)).le)
    (fun n => recursiveTestBudget_le_initial ε n (ts n)) (summable_geometric_test_budget ε)

 theorem tsum_recursive_test_budget_le {ε : ℝ} (hε : 0 < ε)
    (ts : ℕ → List ℝ) (hts : ∀ n t, t ∈ ts n → 0 < t) :
    (∑' n, recursiveTestBudget ε n (ts n)) ≤ ε/4 := by
  rw [← tsum_geometric_test_budget]
  exact (summable_recursive_test_budget hε ts hts).tsum_le_tsum
    (fun n => recursiveTestBudget_le_initial ε n (ts n)) (summable_geometric_test_budget ε)

end CircleDomainRigidity

end

end OAI
