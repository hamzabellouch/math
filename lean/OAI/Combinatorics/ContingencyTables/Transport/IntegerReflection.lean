import OAI.Combinatorics.ContingencyTables.Transport.IntegerMarginal

namespace OAI

/-!
# Actual box reflection and integer addition signatures

Reflection of every coordinate converts a valid two-addition entry into a
two-removal entry. A balanced summed pair is reflected by reversing its
finite index, so the same marginal closure applies to additions.
-/

namespace ContingencyTables.IntegerReflection

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal

variable {I : Type*} [Fintype I] [DecidableEq I]

def reflect (N z : I → ℕ) : I → ℕ := fun i => N i-z i

omit [Fintype I] in
lemma reflect_removeTwo (N r n : I → ℕ) (hr : ∀ i, r i+n i=N i)
    (i j : I) (hv : ValidPair n i j) :
    reflect N (removeTwo n i j) = addTwo r i j := by
  funext k
  have hk := hr k
  have hi := hv.1
  have hj := hv.2
  by_cases hij : i=j
  · subst j
    have hn : 2 ≤ n i := by simp at hj; omega
    by_cases hki : k=i
    · subst k
      simp only [reflect,removeTwo,removeOne,addTwo,ite_true]
      omega
    · simp [reflect,removeTwo,removeOne,addTwo,hki]
      omega
  · have hj0 : 0 < n j := by simpa [Ne.symm hij] using hj
    by_cases hki : k=i
    · subst k
      simp only [reflect,removeTwo,removeOne,addTwo,ite_true,hij,ite_false]
      omega
    · by_cases hkj : k=j
      · subst k
        simp only [reflect,removeTwo,removeOne,addTwo,ite_true,Ne.symm hij,ite_false]
        omega
      · simp only [reflect,removeTwo,removeOne,addTwo,hki,hkj,ite_false,Nat.sub_zero,add_zero]
        omega

omit [Fintype I] in
/-- Exact matrix identity, including all invalid pair entries. -/
theorem addition_eq_reflected_removal (h : (I → ℕ) → ℝ) (N r n : I → ℕ)
    (hr : ∀ i, r i+n i=N i) :
    integerAdditionMatrix h r n = integerRemovalMatrix (fun z => h (reflect N z)) n := by
  ext i j
  unfold integerAdditionMatrix integerRemovalMatrix
  split_ifs with hv
  · dsimp only
    rw [reflect_removeTwo N r n hr i j hv]
  · rfl

/-- The addition signature follows from the raw removal signature of
its globally reflected weight, without a binary-lift assumption. -/
theorem addition_onePositive_of_reflection (h : (I → ℕ) → ℝ) (N r n : I → ℕ)
    (hr : ∀ i, r i+n i=N i)
    (hsig : OnePositiveDirection (integerRemovalMatrix (fun z => h (reflect N z)) n).toBilin') :
    OnePositiveDirection (integerAdditionMatrix h r n).toBilin' := by
  rw [addition_eq_reflected_removal h N r n hr]
  exact hsig

omit [Fintype I] [DecidableEq I] in
lemma reflect_profile (N z : I → ℕ) (M j : ℕ) (hj : j ≤ M) :
    reflect (profile N M M) (profile z j (M-j)) = profile (reflect N z) (M-j) j := by
  funext t
  rcases t with i | (_ | _) <;> simp [reflect,profile]
  omega

omit [Fintype I] [DecidableEq I] in
/-- Reflection commutes with actual balanced marginalization by reversal
of the finite summation index. -/
theorem marginal_reflect (F : ((I ⊕ Bool) → ℕ) → ℝ) (N z : I → ℕ) (M : ℕ) :
    marginal (fun x => F (reflect (profile N M M) x)) M z =
      marginal F M (reflect N z) := by
  unfold marginal
  calc
    _ = ∑ j ∈ Finset.range (M+1), F (profile (reflect N z) (M-j) j) := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only
      rw [reflect_profile N z M j (by simpa using Finset.mem_range.mp hj)]
    _ = _ := by
      have hh := Finset.sum_range_reflect
        (fun j => F (profile (reflect N z) j (M-j))) (M+1)
      convert hh using 1
      apply Finset.sum_congr rfl
      intro j hj
      have hjM : j ≤ M := by simpa using Finset.mem_range.mp hj
      congr 1
      congr 1; omega

end ContingencyTables.IntegerReflection

end OAI
