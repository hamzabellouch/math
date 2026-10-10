import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseBernoulliRun
import OAI.Combinatorics.KMedian.Probability.BernoulliListOperations
import OAI.Combinatorics.KMedian.Sparse.SparseIterationHeight

namespace OAI


                                          
section
namespace MetricKMedian.SparseBernoulli
open Binary
variable {n d : ℕ}

theorem features_height (q : Fin n → Bool) (a : Fin ((n+1)^d)) : HasHeight (features q a) 0 := by
  unfold features monomial
  rw [ListOperation.flag_product]
  split_ifs
  · exact HasHeight.one 0
  · exact HasHeight.zero 0

def stepHeight (n d L : ℕ) := SparseIntegerLaw.stepHeight ((n+1)^d+1) ((n+1)^d) L 0

theorem denominator_height (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (L : ℕ) (hL : ∀ i, HasHeight (p i) L) (t : ℕ) :
    (run (d:=d) p hp t).law.denominator ≤ (2:ℤ)^(stepHeight n d L*t) := by
  induction t with
  | zero => simp [run,SparseIntegerLaw.dirac]
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · rw [dite_eq_left ht]
      have h := SparseIntegerLaw.step_denominator_height (run (d:=d) p hp t) (features (d:=d))
        (fun _ => p ⟨t,ht⟩) (fun _ => hp ⟨t,ht⟩) (fun q b => endpoint q ⟨t,ht⟩ b)
        ((n+1)^d+1) L 0 (run_length p hp t) (fun _ => hL _) (fun _ _ _ => features_height _ _)
      apply h.trans
      calc
        _ ≤ (2:ℤ)^(stepHeight n d L*t)*(2:ℤ)^(stepHeight n d L) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
        _ = _ := by rw [← pow_add,Nat.mul_succ]
    · rw [dite_eq_right ht]
      exact ih.trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (Nat.le_succ t)))

end MetricKMedian.SparseBernoulli
end

end OAI
