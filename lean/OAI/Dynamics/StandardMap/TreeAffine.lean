import OAI.Dynamics.StandardMap.TreeLine

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
lemma tree_chain_additive {d : ℝ → ℝ → ℝ} (hd : TreeLine d) (x : ℕ → ℝ) (N : ℕ)
    (he : ∀ i, i<N → 0<d (x i) (x (i+1)))
    (ht : ∀ i, i+1<N → d (x i) (x (i+2))=d (x i) (x (i+1))+d (x (i+1)) (x (i+2))) :
    d (x 0) (x N)=∑ i∈Finset.range N,d (x i) (x (i+1)) := by
  suffices hh : ∀ n≤N,d (x 0) (x n)=∑ i∈Finset.range n,d (x i) (x (i+1)) from hh N le_rfl
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro hn; simp [hd.self]
  | one => intro hn; simp
  | more n h0 h1 =>
    intro hn
    have hn0 : n≤N := by omega
    have hn1 : n+1≤N := by omega
    have hD0 := h0 hn0
    have hD1 := h1 hn1
    have hp : 0<lineB d (x (n+1)) (x 0) (x n) := by
      unfold lineB
      rw [hd.symm (x (n+1)) (x 0),hd.symm (x (n+1)) (x n),hD0,hD1,Finset.sum_range_succ]
      linarith [he n (by omega)]
    have hz : lineB d (x (n+1)) (x n) (x (n+2))=0 := by
      unfold lineB
      rw [hd.symm (x (n+1)) (x n),ht n (by omega)]
      ring
    have hB := hd.b_nonbacktrack (x (n+1)) (x 0) (x n) (x (n+2)) hp hz
    unfold lineB at hB
    rw [hd.symm (x (n+1)) (x 0),hD1] at hB
    rw [show n+2=(n+1)+1 by omega,Finset.sum_range_succ]
    linarith
lemma tree_chain_affine {d : ℝ → ℝ → ℝ} (hd : TreeLine d) (x : ℕ → ℝ) (N : ℕ) (w : ℝ)
    (hw : 0≤w) (hx : ∀ i,i<N → x i<x (i+1))
    (he : ∀ i,i<N → d (x i) (x (i+1))=w*(x (i+1)-x i))
    (ht : ∀ i,i+1<N → d (x i) (x (i+2))=w*(x (i+2)-x i)) :
    d (x 0) (x N)=w*(x N-x 0) := by
  by_cases hw0 : w=0
  · have hh : ∀ n≤N,d (x 0) (x n)=0 := by
      intro n
      induction n with
      | zero => intro hn; exact hd.self _
      | succ n ih =>
        intro hn
        have hb := hd.triangle (x 0) (x n) (x (n+1))
        rw [ih (by omega),he n (by omega),hw0,zero_mul] at hb
        exact le_antisymm (by linarith) (hd.nonneg _ _)
    rw [hw0,zero_mul,hh N le_rfl]
  · have hwP : 0<w := lt_of_le_of_ne hw (Ne.symm hw0)
    have hh := tree_chain_additive hd x N (fun i hi => by rw [he i hi]; exact mul_pos hwP (sub_pos.mpr (hx i hi)))
      (fun i hi => by rw [ht i hi,he i (by omega),he (i+1) (by omega)]; ring)
    rw [hh]
    trans ∑ i∈Finset.range N,w*(x (i+1)-x i)
    · apply Finset.sum_congr rfl; intro i hi; exact he i (Finset.mem_range.mp hi)
    rw [← Finset.mul_sum]
    congr 1
    clear hh he ht hx hwP hw0 hw hd d
    induction N with
    | zero => simp
    | succ N IH => rw [Finset.sum_range_succ,IH]; ring
end StandardMapEntropy

end OAI
