import OAI.Combinatorics.ContingencyTables.Transport.IntegerMarginal

namespace OAI

/-!
# Fixed-total, finite-box balanced marginal closure

The display and positivity hypotheses of integer marginalization follow
from the box-valid total slice. Positivity of the marginal permits induction
over every finite family of balanced pairs before the equality limit.
-/

namespace ContingencyTables.BalancedBox

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal

variable {I : Type*} [Fintype I] [DecidableEq I]

def InBox (m z : I → ℕ) : Prop := ∀ i, z i ≤ m i

def PositiveSlice (f : (I → ℕ) → ℝ) (m : I → ℕ) (R : ℕ) : Prop :=
  ∀ z, InBox m z → (∑ i, z i)=R → 0 < f z

def RemovalSlice (f : (I → ℕ) → ℝ) (m : I → ℕ) (R : ℕ) : Prop :=
  ∀ z, InBox m z → (∑ i, z i)=R+2 →
    OnePositiveDirection (integerRemovalMatrix f z).toBilin'

omit [Fintype I] [DecidableEq I] in
lemma profile_inBox (m z : I → ℕ) (M a b : ℕ) (hz : InBox m z) (ha : a ≤ M) (hb : b ≤ M) :
    InBox (profile m M M) (profile z a b) := by
  intro i
  rcases i with i | (_ | _) <;> simp only [profile,Sum.elim_inl,Sum.elim_inr,ite_true]
  · exact hz i
  · exact ha
  · exact hb

omit [DecidableEq I] in
lemma profile_total (z : I → ℕ) (a b : ℕ) :
    (∑ i, profile z a b i)=(∑ i, z i)+a+b := by
  simp [profile,Fintype.sum_sum_type]
  omega

/-- One balanced pair preserves the exact box-valid integer signature. -/
theorem marginal_removal_slice (F : ((I ⊕ Bool) → ℕ) → ℝ) (m : I → ℕ) (R M : ℕ)
    (hM : 2 ≤ M) (hpos : PositiveSlice F (profile m M M) (R+M))
    (hsig : RemovalSlice F (profile m M M) (R+M)) :
    RemovalSlice (marginal F M) m R := by
  intro z hz htotal
  apply marginal_removal_onePositive F M z hM
  · intro j hj
    apply hsig _ (profile_inBox m z M j (M-j) hz hj (Nat.sub_le _ _))
    rw [profile_total,htotal]
    omega
  · intro j hj0 hjM
    apply hpos _ (profile_inBox m z M (j-1) (M-1-j) hz (by omega) (by omega))
    rw [profile_total,htotal]
    omega

omit [DecidableEq I] in
/-- The finite sum stays strictly positive on precisely its required total
slice. This is the induction input for the next balanced pair. -/
theorem marginal_positive_slice (F : ((I ⊕ Bool) → ℕ) → ℝ) (m : I → ℕ) (R M : ℕ)
    (hpos : PositiveSlice F (profile m M M) (R+M)) :
    PositiveSlice (marginal F M) m R := by
  intro z hz htotal
  unfold marginal
  apply Finset.sum_pos'
  · intro j hj
    have hjM : j ≤ M := by simpa using Finset.mem_range.mp hj
    apply le_of_lt
    apply hpos _ (profile_inBox m z M j (M-j) hz hjM (Nat.sub_le _ _))
    rw [profile_total,htotal]
    omega
  · refine ⟨0,by simp,?_⟩
    apply hpos _ (profile_inBox m z M 0 (M-0) hz (Nat.zero_le _) (by simp))
    rw [profile_total,htotal]
    omega

end ContingencyTables.BalancedBox

end OAI
