import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseGraphLaw
import OAI.Combinatorics.KMedian.Compression.RationalOperationHeight

namespace OAI


                                      
section
namespace MetricKMedian.SparseGraph
open Binary
variable {n m : ℕ}

theorem edge_height (G : Graph n m) (h : Fin n) (i : Fin m) : HasHeight (edge G h i) 0 := by
  unfold edge
  split_ifs
  · exact HasHeight.one 0
  · exact HasHeight.zero 0

theorem features_height (G : Graph n m) (a : Fin (n*m+(n*m)*(n*m))) : HasHeight (features G a) 0 := by
  unfold features edgeCode
  generalize finSumFinEquiv.symm a=z
  cases z with
  | inl i => exact edge_height _ _ _
  | inr ij => exact (edge_height _ _ _).mul (edge_height _ _ _)

def stepHeight (n m N L : ℕ) :=
  let d := n*m+(n*m)*(n*m)
  L+((2*(d+1)*(d+1))*((d+1)*N+1))*((d+1)*N)

theorem denominator_height (ν : Fin m → SparseIntegerLaw (Finset (Fin n))) (N L : ℕ)
    (hN : ∀ i, (ν i).length≤N) (hL : ∀ i, (ν i).law.denominator≤(2:ℤ)^L) (t : ℕ) :
    (run ν t).law.denominator≤(2:ℤ)^(stepHeight n m N L*t) := by
  induction t with
  | zero => simp [run,SparseIntegerLaw.dirac]
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · rw [dite_eq_left ht]
      let μ := run ν t
      let ρ := μ.prod (ν ⟨t,ht⟩) (fun G S => next G S ⟨t,ht⟩)
      have hc := ρ.compressAuto_denominator features 0
        (fun i a => (features_height ρ.states[i.val] a).1)
        (fun i a => (features_height ρ.states[i.val] a).2)
      simp only [zero_mul,add_zero] at hc
      have hrD : ρ.law.denominator=μ.law.denominator*(ν ⟨t,ht⟩).law.denominator := rfl
      have hrN : ρ.length ≤ (n*m+(n*m)*(n*m)+1)*N :=
        Nat.mul_le_mul (run_length ν t) (hN _)
      change (ρ.compressAuto features).law.denominator≤_
      apply hc.trans
      rw [hrD]
      calc
        _ ≤ ((2:ℤ)^(stepHeight n m N L*t)*(2:ℤ)^L)*
            (2:ℤ)^((2*(n*m+(n*m)*(n*m)+1)*(n*m+(n*m)*(n*m)+1))*
              ((n*m+(n*m)*(n*m)+1)*N+1)*((n*m+(n*m)*(n*m)+1)*N)) := by
          gcongr
          · exact (ν ⟨t,ht⟩).law.denominator_pos.le
          · exact hL _
          · norm_num
        _ = _ := by rw [← pow_add,← pow_add]; congr 1; simp only [stepHeight]; ring
    · rw [dite_eq_right ht]
      exact ih.trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (Nat.le_succ t)))
end MetricKMedian.SparseGraph
end

end OAI
