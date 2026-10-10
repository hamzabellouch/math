import OAI.Analysis.Triangular.Basic

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.PolynomialShift
lemma shift_sum {N M d : ℕ} (hd : N+d≤M) (a : ℕ → ℝ) (τ : ℝ) :
    (∑ l : Fin (M+1), (if d≤l.val ∧ l.val-d≤N then a (l.val-d) else 0)*τ^l.val) =
      τ^d * ∑ i : Fin (N+1), a i.val*τ^i.val := by
  have he (l : Fin (M+1)) :
      (if d≤l.val ∧ l.val-d≤N then a (l.val-d) else 0) =
        ∑ i : Fin (N+1), if l.val=i.val+d then a i.val else 0 := by
    by_cases hl : d≤l.val ∧ l.val-d≤N
    · rw [ite_eq_left hl]
      symm
      rw [Finset.sum_eq_single (⟨l.val-d,by omega⟩ : Fin (N+1))]
      · simp only [Nat.sub_add_cancel hl.1,ite_true]
      · intro b _ hb
        rw [ite_eq_right]
        intro h
        apply hb
        apply Fin.ext
        change b.val = l.val-d
        omega
      · simp
    · rw [ite_eq_right hl]
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [ite_eq_right]
      omega
  simp_rw [he,Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  trans ∑ i : Fin (N+1), a i.val*τ^(i.val+d)
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single (⟨i.val+d,by omega⟩ : Fin (M+1))]
    · simp
    · intro b _ hb
      rw [ite_eq_right]
      intro h
      exact hb (Fin.ext h)
    · simp
  · simp_rw [pow_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
end AtomicTriangular.PolynomialShift
end

end OAI
