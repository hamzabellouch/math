import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparsePhysicalBatch

namespace OAI

namespace MetricKMedian.SparsePhysicalBatch
open Finset
variable {n : ℕ}

theorem marginal_le (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) {Q : ℝ}
    (hpQ : (p:ℝ) ≤ Q) (hqQ : ∀ e, (q e:ℝ) ≤ Q) (e : Fin n) :
    (law Z C p q hp hq).real.prob (fun A => e∈A) ≤ Q/2 := by
  rw [marginal]
  split_ifs with he
  · have hm := SparseBernoulli.real_marginal (d := 4) (fun _ : Fin n => p)
      (fun _ => hp) (by norm_num) e
    have hh : (SparseBernoulli.run (d := 4) (fun _ => p) (fun _ => hp) n).real.prob
        (fun ω => e∈FiniteLaw.selected C ω) ≤ (p:ℝ) := by
      rw [← hm]
      apply FiniteLaw.prob_mono
      intro ω h
      simp only [FiniteLaw.selected,mem_filter,mem_univ,true_and] at h
      exact h.1
    linarith only [hh,hpQ]
  · linarith only [hqQ e]

end MetricKMedian.SparsePhysicalBatch

end OAI
