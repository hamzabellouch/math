import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.RegularDualWitness

namespace OAI

namespace MetricKMedianRecovery

theorem valid_execution_final_dual
    {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    {steps : ℕ} (v lam eta : ℝ) (E : ValidExecution D X steps v lam eta)
    (hv : 0 < v) (hv1 : v < 1 / 6) (hlam : 0 < lam)
    (i : X) (hi : i ∈ E.regular) :
    (∑ j, max ((E.state steps).budget j - 2 * dist i (E.location j)) 0) ≤ lam := by
  classical
  let C := Finset.univ.filter (E.Contributor i)
  have heq : (∑ j, max ((E.state steps).budget j - 2 * dist i (E.location j)) 0) =
      ∑ j ∈ C, (E.finalBudget j - 2 * dist i (E.location j)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    change max (E.finalBudget j - 2 * dist i (E.location j)) 0 = _
    by_cases hc : E.Contributor i j
    · rw [ite_eq_left hc, max_eq_left (sub_nonneg.mpr hc.le)]
    · rw [ite_eq_right hc, max_eq_right (sub_nonpos.mpr (not_lt.mp hc))]
  rw [heq]
  by_cases hC : C.Nonempty
  · exact E.contributor_dual_bound hv hv1 hlam i hi C hC
      (fun _ hj => (Finset.mem_filter.mp hj).2)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hC, Finset.sum_empty]
    exact hlam.le

end MetricKMedianRecovery

end OAI
