import OAI.Dynamics.StandardMap.MatchingQuantitative

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma endpoint_shortfall_bounds (M : ℝ) (v : ℕ → ℝ) (b : ℝ) (n N : ℕ)
    (hn : 10000000 ≤ n) (hN : n ≤ N ∧ N ≤ n+1) (hM : 6 ≤ M)
    (hv : ∀ j, 1 ≤ j → j < N → |v j|+1 ≤ M)
    (hb : pairMagnitude (linearSolution v 1 b) N ≤ 3*M^(-((1-3/100000000:ℝ)*(n:ℝ)))) :
    (N:ℝ)-1-pairLog M (tSolution v) N ≤ (n:ℝ)/1000 ∧
      (badIndices M v b N).card ≤ n/1000 := by
  have hm : 1 < M := by linarith
  have hm0 : 0 < M := by linarith
  have hlog2 : Real.logb M 2 ≤ 1 := by
    rw [← Real.logb_self_eq_one hm]
    exact (Real.logb_le_logb hm (by norm_num) hm0).mpr (by linarith)
  have hlog3 : Real.logb M 3 ≤ 1 := by
    rw [← Real.logb_self_eq_one hm]
    exact (Real.logb_le_logb hm (by norm_num) hm0).mpr (by linarith)
  have hnR : (10000000:ℝ) ≤ n := by exact_mod_cast hn
  have hNR : (N:ℝ) ≤ (n:ℝ)+1 := by exact_mod_cast hN.2
  have ht:=small_endpoint_log_bounds v b M (3*M^(-((1-3/100000000:ℝ)*(n:ℝ)))) N hm (by omega) (by positivity) hb
  have he : Real.logb M (3*M^(-((1-3/100000000:ℝ)*(n:ℝ)))) =
      Real.logb M 3-(1-3/100000000:ℝ)*(n:ℝ) := by
    rw [Real.logb_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hm0 _)),Real.logb_rpow hm0 hm.ne']
    ring
  rw [he] at ht
  have hg:=many_good_small_endpoint v b M ((1-3/100000000:ℝ)*(n:ℝ)) N (by omega) hm hv hb
  norm_num [goodExponent] at hg
  constructor
  · linarith [ht.1]
  · have htin : ((badIndices M v b N).card:ℝ) ≤ (n:ℝ)/1000-1 := by linarith
    have he' : (n:ℝ)/1000-1 < (↑(n/1000):ℝ)+1 := by
      have hnn : n ≤ 1000*(n/1000)+999 := by omega
      have hnnR : (n:ℝ) ≤ 1000*(↑(n/1000):ℝ)+999 := by exact_mod_cast hnn
      linarith
    have hlt : (badIndices M v b N).card < n/1000+1 := by exact_mod_cast htin.trans_lt he'
    omega
lemma matching_small_endpoints (M : ℝ) (vp vm : ℕ → ℝ) (bp bm : ℝ)
    (n Np Nm : ℕ) (hn : 10000000 ≤ n) (hNp : n ≤ Np ∧ Np ≤ n+1)
    (hNm : n ≤ Nm ∧ Nm ≤ n+1) (hM : 6 ≤ M)
    (hvp : ∀ j, 1 ≤ j → j < Np → |vp j|+1 ≤ M)
    (hvm : ∀ j, 1 ≤ j → j < Nm → |vm j|+1 ≤ M)
    (hbp : pairMagnitude (linearSolution vp 1 bp) Np ≤ 3*M^(-((1-3/100000000:ℝ)*(n:ℝ))))
    (hbm : pairMagnitude (linearSolution vm 1 bm) Nm ≤ 3*M^(-((1-3/100000000:ℝ)*(n:ℝ)))) :
    ∃ (T : Finset ℕ) (f : ℕ → ℕ), n/100 ≤ T.card ∧
      (∀ j ∈ T, 2 ≤ j ∧ j ≤ Np-2 ∧ GoodIndex M vp bp j ∧
        2 ≤ f j ∧ f j ≤ Nm-2 ∧ GoodIndex M vm bm (f j) ∧
        |pairLog M (tSolution vp) j-pairLog M (tSolution vm) (f j)| ≤ 1/2) ∧
      (∀ i ∈ T, ∀ j ∈ T, i < j → f i < f j) := by
  have hp:=endpoint_shortfall_bounds M vp bp n Np hn hNp hM hvp hbp
  have hm:=endpoint_shortfall_bounds M vm bm n Nm hn hNm hM hvm hbm
  exact matching_of_shortfalls M vp vm bp bm n Np Nm (by omega) hNp hNm (by linarith)
    hvp hvm hp.1 hm.1 hp.2 hm.2
end StandardMapEntropy

end OAI
