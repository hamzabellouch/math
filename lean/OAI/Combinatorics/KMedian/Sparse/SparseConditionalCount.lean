import Mathlib
import OAI.Combinatorics.KMedian.Process.CountTail
import OAI.Combinatorics.KMedian.Sparse.SparseCountStatistic

namespace OAI

section
section
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

theorem conditional_count_tail (q a m : Fin n → ℚ) (c : Fin n → Fin n → ℚ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) {D p φ g A b : ℝ}
    (hD : 1 ≤ D) (hp : 0 < p) (hφ : 0 < φ) (hg : 0 < g) (hb : 0 < b)
    (hlarge : 1 < b*A) (hqP : ∀ i, (q i:ℝ) ≤ 2*p)
    (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
    (hsize : ∀ i, (a i:ℝ)+(m i:ℝ) ≤ b*A+2)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, (c i j:ℝ) ≤ (D-1)*(m i:ℝ))
    (hmass : (∑ i, (m i:ℝ)) ≤ 2*A/g)
    (htotal : (∑ i, ((a i:ℝ)+(m i:ℝ))) ≤ 4*A/g)
    (hsmall : 8*p*D ≤ φ*g)
    (hlinear : (∑ i, ((a i:ℝ)-(m i:ℝ))*(q i:ℝ)) ≤ -p*φ*A) :
    (run (d := 4) q hq n).real.prob (fun ω => 0 <
      CountStatistic.statistic (fun i => (a i:ℝ)-(m i:ℝ)) (fun i j => (c i j:ℝ)) ω) ≤
      96*D^2*b/(p*φ^2*g) := by
  have hA : 0 < A := (mul_pos_iff_of_pos_left hb).mp (lt_trans (by norm_num) hlarge)
  have ht : 0 < p*φ*A/2 := by positivity
  have hM : 0 ≤ ∑ i, (m i:ℝ) := sum_nonneg (fun i _ => by exact_mod_cast hm i)
  have hov := CountStatistic.overlap_budget hp.le hg hA.le hD hM hmass hsmall
  have hlin : (∑ i, ((a i:ℝ)-(m i:ℝ))*(q i:ℝ)) ≤
      -(p*φ*A/2)-(1/2)*(2*p)^2*(D-1)*∑ i, (m i:ℝ) := by
    linarith only [hlinear,hov]
  have hprob := count_failure q a m c hq hD (by positivity) ht hqP ha hm
    hsize hc hdiag hc0 hrow hlin
  apply hprob.trans
  have hsum : 0 ≤ ∑ i, ((a i:ℝ)+(m i:ℝ)) := by
    apply sum_nonneg
    intro i _
    exact add_nonneg (by exact_mod_cast ha i) (by exact_mod_cast hm i)
  have hB : b*A+2 ≤ 3*b*A := by linarith only [hlarge]
  calc
    (2*p)*D^2*(b*A+2)*(∑ i, ((a i:ℝ)+(m i:ℝ)))/(p*φ*A/2)^2 ≤
        (2*p)*D^2*(3*b*A)*(4*A/g)/(p*φ*A/2)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hB (by positivity)) htotal hsum (by positivity)
    _ = 96*D^2*b/(p*φ^2*g) := by
      field_simp
      ring

end MetricKMedian.SparseBernoulli
end
end

end OAI
