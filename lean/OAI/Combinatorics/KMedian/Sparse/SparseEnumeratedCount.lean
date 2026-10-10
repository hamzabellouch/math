import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseMixture
import OAI.Combinatorics.KMedian.Sparse.SparseConditionalCount

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedBernoulli
open Finset
variable {E : Type} [Fintype E] [DecidableEq E] {n : ℕ}

def law (enum : Fin n ≃ E) (q : E → ℚ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) :
    SparseIntegerLaw (E → Bool) :=
  (SparseBernoulli.run (d := 4) (fun a => q (enum a)) (fun a => hq (enum a)) n).map
    (fun ω e => ω (enum.symm e))

omit [DecidableEq E] in
theorem statistic_reindex (enum : Fin n ≃ E) (a : E → ℝ) (c : E → E → ℝ)
    (ω : Fin n → Bool) :
    CountStatistic.statistic a c (fun e => ω (enum.symm e))=
      CountStatistic.statistic (fun i => a (enum i)) (fun i j => c (enum i) (enum j)) ω := by
  unfold CountStatistic.statistic
  rw [← enum.sum_comp (fun e => a e * CountStatistic.bit (fun e => ω (enum.symm e)) e)]
  simp only [CountStatistic.bit,Equiv.symm_apply_apply]
  congr 1
  congr 1
  rw [← enum.sum_comp]
  apply sum_congr rfl
  intro i _
  rw [← enum.sum_comp]
  simp only [Equiv.symm_apply_apply]

theorem conditional_count_tail (enum : Fin n ≃ E) (q a m : E → ℚ) (c : E → E → ℚ)
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
    (law enum q hq).real.prob (fun ω => 0 <
      CountStatistic.statistic (fun i => (a i:ℝ)-(m i:ℝ)) (fun i j => (c i j:ℝ)) ω) ≤
      96*D^2*b/(p*φ^2*g) := by
  rw [law,SparseIntegerLaw.prob_map]
  simp only [statistic_reindex]
  apply SparseBernoulli.conditional_count_tail (fun i => q (enum i))
    (fun i => a (enum i)) (fun i => m (enum i)) (fun i j => c (enum i) (enum j))
    (fun i => hq (enum i)) hD hp hφ hg hb hlarge (fun i => hqP (enum i))
    (fun i => ha (enum i)) (fun i => hm (enum i)) (fun i => hsize (enum i))
    (fun i j => hc (enum i) (enum j)) (fun i => hdiag (enum i))
    (fun i j => hc0 (enum i) (enum j))
  · intro i
    rw [enum.sum_comp (fun j => (c (enum i) j:ℝ))]
    exact hrow (enum i)
  · rw [enum.sum_comp (fun i => (m i:ℝ))]
    exact hmass
  · rw [enum.sum_comp (fun i => (a i:ℝ)+(m i:ℝ))]
    exact htotal
  · exact hsmall
  · rw [enum.sum_comp (fun i => ((a i:ℝ)-(m i:ℝ))*(q i:ℝ))]
    exact hlinear

end MetricKMedian.SparseEnumeratedBernoulli
end
end

end OAI
