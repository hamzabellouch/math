import OAI.Dynamics.StandardMap.TransportCarry

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma liftIter_neg_swap (k : ℝ) (n : ℕ) (z : ℝ × ℝ) :
    liftIter k (-(n:ℤ)) z=(liftIter k (n:ℤ) z.swap).swap := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show ((n+1:ℕ):ℤ)=1+(n:ℤ) by omega,show -(1+(n:ℤ))=(-1)+(-(n:ℤ)) by ring,
      liftIter_add,liftIter_add,ih]
    simp only [liftIter,zpow_neg_one,zpow_one,Equiv.Perm.inv_def,liftStep_symm_apply,liftStep_apply,
      Prod.fst_swap,Prod.snd_swap,Prod.swap_prod_mk]
lemma graph_endpoint_close (k : ℝ) (hk : 0 ≤ k) (z w : ℝ × ℝ) (n B : ℕ) (hn : 1 ≤ n)
    (hB : B=n ∨ B=n+1)
    (hterm : liftedOrbit k z.2 z.1 (n+1)=liftedOrbit k w.2 w.1 (n+1))
    (hbound : ∀ i : Fin n,
      |liftedOrbit k z.2 z.1 (i+1)-liftedOrbit k w.2 w.1 (i+1)| ≤
        8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) :
    dist (liftIter k (B:ℤ) z) (liftIter k (B:ℤ) w) ≤
      8/growthBase k^((4/5:ℝ)*(B-1:ℕ)) := by
  have hM : 1 ≤ growthBase k := by have := growthBase_ge_four k hk; linarith
  have hMn : 0 ≤ 8/growthBase k^((4/5:ℝ)*(n:ℝ)) := by positivity
  have hn' : n-1+1=n := by omega
  have hlast := hbound (⟨n-1,by omega⟩ : Fin n)
  have hreal : ((n-1:ℕ):ℝ)+1=n := by exact_mod_cast hn'
  simp only [hn',hreal] at hlast
  have he : dist (liftIter k (B:ℤ) z) (liftIter k (B:ℤ) w) ≤
      8/growthBase k^((4/5:ℝ)*(n:ℝ)) := by
    rcases hB with rfl|rfl
    · rw [liftIter_nat,liftIter_nat,Prod.dist_eq,Real.dist_eq,Real.dist_eq,hterm,sub_self,abs_zero]
      exact max_le hMn hlast
    · rw [liftIter_nat,liftIter_nat,Prod.dist_eq,Real.dist_eq,Real.dist_eq,liftedOrbit_step,
        liftedOrbit_step,hterm,sub_self,abs_zero]
      have he : |phi k (liftedOrbit k w.2 w.1 (n+1))-liftedOrbit k z.2 z.1 n-
          (phi k (liftedOrbit k w.2 w.1 (n+1))-liftedOrbit k w.2 w.1 n)| =
          |liftedOrbit k z.2 z.1 n-liftedOrbit k w.2 w.1 n| := by
        rw [sub_sub_sub_cancel_left,abs_sub_comm]
      rw [he]
      exact max_le hlast hMn
  apply he.trans
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hM
  have hle : (B-1:ℕ) ≤ n := by rcases hB with rfl|rfl <;> omega
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (by norm_num)
lemma graph_backward_endpoint_close (k : ℝ) (hk : 0 ≤ k) (z w : ℝ × ℝ) (n B : ℕ) (hn : 1 ≤ n)
    (hB : B=n ∨ B=n+1)
    (hterm : liftedOrbit k z.1 z.2 (n+1)=liftedOrbit k w.1 w.2 (n+1))
    (hbound : ∀ i : Fin n,
      |liftedOrbit k z.1 z.2 (i+1)-liftedOrbit k w.1 w.2 (i+1)| ≤
        8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) :
    dist (liftIter k (-(B:ℤ)) z) (liftIter k (-(B:ℤ)) w) ≤
      8/growthBase k^((4/5:ℝ)*(B-1:ℕ)) := by
  rw [liftIter_neg_swap,liftIter_neg_swap]
  simpa only [Prod.dist_eq,Prod.fst_swap,Prod.snd_swap,max_comm] using graph_endpoint_close k hk z.swap w.swap n B hn hB hterm hbound
end StandardMapEntropy

end OAI
