import OAI.NumberTheory.Jacobsthal.Partitions.SourceLabelCount

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseRefinement
open ErdosInverseCells
attribute [local instance] Classical.decEq

theorem dense_fiber_after_count_discard {ι : Type*} [Fintype ι]
    (C : Finset ℕ) (label : ℕ → ι) (tau rho eta d : ℝ) (hC : 0 < C.card) (heta : 0 ≤ eta)
    (hgap : eta+d < rho) (f : ℕ → ℝ) (hf : ∀ q ∈ C,f q ≤ 1)
    (hMass : rho*(C.card : ℝ) ≤ ∑ q ∈ C,f q)
    (hDiscard : ((discardedPoints C label tau).card : ℝ) ≤ d*(C.card : ℝ)) :
    ∃ i : ι,tau ≤ ((labelFiber C label i).card : ℝ) ∧
      eta*((labelFiber C label i).card : ℝ) < ∑ q ∈ labelFiber C label i,f q := by
  classical
  by_contra hno
  push Not at hno
  have hcell : ∀ i : ι,(∑ q ∈ labelFiber C label i,f q) ≤ eta*((labelFiber C label i).card : ℝ)+
      (if ((labelFiber C label i).card : ℝ) < tau then ((labelFiber C label i).card : ℝ) else 0) := by
    intro i
    by_cases hi : ((labelFiber C label i).card : ℝ) < tau
    · rw [ite_eq_left hi]
      have hfi : (∑ q ∈ labelFiber C label i,f q) ≤ ((labelFiber C label i).card : ℝ) := by
        simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using
          Finset.sum_le_sum (fun q hq => hf q (labelFiber_subset C label i hq))
      nlinarith [show (0 : ℝ) ≤ (labelFiber C label i).card from Nat.cast_nonneg _]
    · rw [ite_eq_right hi,add_zero]
      exact hno i (le_of_not_gt hi)
  have hcard : (∑ i : ι,((labelFiber C label i).card : ℝ)) = (C.card : ℝ) := by
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using sum_label_fibers C label (fun _ => (1 : ℝ))
  have hsmall : (∑ i : ι,if ((labelFiber C label i).card : ℝ) < tau then ((labelFiber C label i).card : ℝ) else 0) =
      ((discardedPoints C label tau).card : ℝ) := by
    have hh := sum_small_fibers C label tau (fun _ => (1 : ℝ))
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one,smallLabels,Finset.sum_filter] using hh
  have hsum : (∑ q ∈ C,f q) ≤ eta*(C.card : ℝ)+((discardedPoints C label tau).card : ℝ) := by
    calc
      _ = ∑ i : ι,∑ q ∈ labelFiber C label i,f q := (sum_label_fibers C label f).symm
      _ ≤ ∑ i : ι,(eta*((labelFiber C label i).card : ℝ)+
          (if ((labelFiber C label i).card : ℝ) < tau then ((labelFiber C label i).card : ℝ) else 0)) :=
        Finset.sum_le_sum (fun i _ => hcell i)
      _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,hcard,hsmall]
  have hCp : (0 : ℝ) < C.card := by exact_mod_cast hC
  have hstrict := mul_lt_mul_of_pos_right hgap hCp
  nlinarith

end ErdosInverseRefinement

end

end Erdos970

end OAI
