import OAI.Combinatorics.ContingencyTables.Transport.BalancedSummation
import OAI.Combinatorics.ContingencyTables.Transport.FactorialSignatures

namespace OAI

/-!
# Balanced marginalization of actual integer two-removal matrices

The new pair is summed subject to its exact total M. We identify every
old, fresh and cross entry with the balanced summation theorem; thus the
signature of the marginal is derived from signatures of the actual unsummed
integer matrices, rather than assumed for a binary encoding.
-/

namespace ContingencyTables.IntegerMarginal

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures
open LinearMap (BilinForm)

variable {I : Type*} [Fintype I] [DecidableEq I]

def profile (z : I → ℕ) (a b : ℕ) : I ⊕ Bool → ℕ :=
  Sum.elim z (fun t => if t then b else a)

noncomputable def marginal (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ) : ℝ :=
  ∑ j ∈ Finset.range (M + 1), F (profile z j (M-j))

omit [Fintype I] in
lemma profile_removeOld (z : I → ℕ) (a b : ℕ) (i k : I) :
    removeTwo (profile z a b) (.inl i) (.inl k) = profile (removeTwo z i k) a b := by
  funext t
  rcases t with i | (_ | _) <;> simp [profile,removeTwo,removeOne]

omit [Fintype I] in
lemma profile_removeAA (z : I → ℕ) (a b : ℕ) :
    removeTwo (profile z a b) (.inr false) (.inr false) = profile z (a-2) b := by
  funext t
  rcases t with i | (_ | _) <;> simp [profile,removeTwo,removeOne]
  omega

omit [Fintype I] in
lemma profile_removeBB (z : I → ℕ) (a b : ℕ) :
    removeTwo (profile z a b) (.inr true) (.inr true) = profile z a (b-2) := by
  funext t
  rcases t with i | (_ | _) <;> simp [profile,removeTwo,removeOne]
  omega

omit [Fintype I] in
lemma profile_removeAB (z : I → ℕ) (a b : ℕ) :
    removeTwo (profile z a b) (.inr false) (.inr true) = profile z (a-1) (b-1) := by
  funext t
  rcases t with i | (_ | _) <;> simp [profile,removeTwo,removeOne]

omit [Fintype I] in
lemma profile_removeOldA (z : I → ℕ) (a b : ℕ) (i : I) :
    removeTwo (profile z a b) (.inl i) (.inr false) = profile (removeOne z i) (a-1) b := by
  funext t
  rcases t with i | (_ | _) <;> simp [profile,removeTwo,removeOne]

omit [Fintype I] in
lemma profile_removeOldB (z : I → ℕ) (a b : ℕ) (i : I) :
    removeTwo (profile z a b) (.inl i) (.inr true) = profile (removeOne z i) a (b-1) := by
  funext t
  rcases t with i | (_ | _) <;> simp [profile,removeTwo,removeOne]

noncomputable def old : (I → ℝ) →ₗ[ℝ] (I ⊕ Bool → ℝ) where
  toFun v := Sum.elim v (fun _ => 0)
  map_add' _ _ := by ext t; cases t <;> simp
  map_smul' _ _ := by ext t; cases t <;> simp

noncomputable def pairMatrix (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) : Matrix (I ⊕ Bool) (I ⊕ Bool) ℝ :=
  integerRemovalMatrix F (profile z j (M-j))

noncomputable def innerWeight (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) : ℝ :=
  if 0 < j ∧ j < M then F (profile z (j-1) (M-1-j)) else 0

noncomputable def cross (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) : (I → ℝ) →ₗ[ℝ] ℝ :=
  if 0 < j ∧ j ≤ M then
    (pairMatrix F M z j).toBilin' |>.flip (Pi.single (.inr false) 1) |>.comp old
  else 0

omit [Fintype I] in
lemma integerRemoval_symm (F : (I → ℕ) → ℝ) (z : I → ℕ) (i k : I) :
    integerRemovalMatrix F z i k = integerRemovalMatrix F z k i := by
  simp only [integerRemovalMatrix, validPair_symm z i k, removeTwo_comm z i k]

omit [Fintype I] in
lemma pairMatrix_aa (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) (hj : j ≤ M) :
    pairMatrix F M z j (.inr false) (.inr false) = innerWeight F M z (j-1) := by
  have hv : ValidPair (profile z j (M-j)) (.inr false) (.inr false) ↔ 2 ≤ j := by
    simp [ValidPair,profile]; omega
  unfold pairMatrix integerRemovalMatrix
  rw [if_congr hv rfl rfl, profile_removeAA]
  unfold innerWeight
  by_cases h : 2 ≤ j
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    congr 1
    congr 1; omega
  · rw [ite_eq_right h, ite_eq_right (by omega)]

omit [Fintype I] in
lemma pairMatrix_bb (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) (hj : j ≤ M) :
    pairMatrix F M z j (.inr true) (.inr true) = innerWeight F M z (j+1) := by
  have hv : ValidPair (profile z j (M-j)) (.inr true) (.inr true) ↔ j+2 ≤ M := by
    simp [ValidPair,profile]; omega
  unfold pairMatrix integerRemovalMatrix
  rw [if_congr hv rfl rfl, profile_removeBB]
  unfold innerWeight
  by_cases h : j+2 ≤ M
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    congr 1
    congr 1; omega
  · rw [ite_eq_right h, ite_eq_right (by omega)]

omit [Fintype I] in
lemma pairMatrix_ab (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) (_hj : j ≤ M) :
    pairMatrix F M z j (.inr false) (.inr true) = innerWeight F M z j := by
  have hv : ValidPair (profile z j (M-j)) (.inr false) (.inr true) ↔ 0 < j ∧ j < M := by
    simp [ValidPair,profile]
  unfold pairMatrix integerRemovalMatrix
  rw [if_congr hv rfl rfl, profile_removeAB]
  unfold innerWeight
  split_ifs
  · congr 1; congr 1; omega
  · rfl

lemma old_single (B : Matrix (I ⊕ Bool) (I ⊕ Bool) ℝ) (v : I → ℝ) (t : Bool) :
    B.toBilin' (old v) (Pi.single (.inr t) 1) = ∑ i, v i * B (.inl i) (.inr t) := by
  simp [Matrix.toBilin'_apply, old, Fintype.sum_sum_type, Pi.single_apply]

lemma old_old (B : Matrix (I ⊕ Bool) (I ⊕ Bool) ℝ) (v w : I → ℝ) :
    B.toBilin' (old v) (old w) = (B.submatrix Sum.inl Sum.inl).toBilin' v w := by
  simp [Matrix.toBilin'_apply, old, Fintype.sum_sum_type]

lemma cross_a (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) (hj : j ≤ M) (v : I → ℝ) :
    (pairMatrix F M z j).toBilin' (old v) (Pi.single (.inr false) 1) = cross F M z j v := by
  unfold cross
  by_cases h : 0 < j
  · rw [ite_eq_left ⟨h,hj⟩]; rfl
  · rw [ite_eq_right (by omega)]
    rw [old_single]
    apply Finset.sum_eq_zero
    intro i _
    have hv : ¬ValidPair (profile z j (M-j)) (.inl i) (.inr false) := by
      simp [ValidPair,profile]; omega
    simp [pairMatrix,integerRemovalMatrix,hv]

lemma cross_b (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) (hj : j ≤ M) (v : I → ℝ) :
    (pairMatrix F M z j).toBilin' (old v) (Pi.single (.inr true) 1) = cross F M z (j+1) v := by
  unfold cross
  by_cases h : j < M
  · rw [ite_eq_left (by omega)]
    change _ = (pairMatrix F M z (j+1)).toBilin' (old v) (Pi.single (.inr false) 1)
    rw [old_single,old_single]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have hv : ValidPair (profile z j (M-j)) (.inl i) (.inr true) ↔ 0 < z i := by
      simp [ValidPair,profile]; omega
    have hv' : ValidPair (profile z (j+1) (M-(j+1))) (.inl i) (.inr false) ↔ 0 < z i := by
      simp [ValidPair,profile]
    unfold pairMatrix integerRemovalMatrix
    rw [if_congr hv rfl rfl,if_congr hv' rfl rfl,profile_removeOldB,profile_removeOldA]
    simp only [Nat.add_sub_cancel,Nat.sub_sub]
  · rw [ite_eq_right (by omega),old_single]
    apply Finset.sum_eq_zero
    intro i _
    have hv : ¬ValidPair (profile z j (M-j)) (.inl i) (.inr true) := by
      simp [ValidPair,profile]; omega
    simp [pairMatrix,integerRemovalMatrix,hv]

omit [Fintype I] in
lemma pairMatrix_old (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ)
    (j : ℕ) (i k : I) :
    pairMatrix F M z j (.inl i) (.inl k) =
      if ValidPair z i k then F (profile (removeTwo z i k) j (M-j)) else 0 := by
  have hv : ValidPair (profile z j (M-j)) (.inl i) (.inl k) ↔ ValidPair z i k := by
    simp [ValidPair,profile]
  unfold pairMatrix integerRemovalMatrix
  rw [if_congr hv rfl rfl,profile_removeOld]

omit [Fintype I] in
lemma marginal_old_matrix (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ) :
    integerRemovalMatrix (marginal F M) z =
      ∑ j ∈ Finset.range (M+1), (pairMatrix F M z j).submatrix Sum.inl Sum.inl := by
  ext i k
  simp only [Matrix.sum_apply,Matrix.submatrix_apply,pairMatrix_old,integerRemovalMatrix,marginal]
  split_ifs <;> simp

lemma marginal_old_block (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ) :
    (integerRemovalMatrix (marginal F M) z).toBilin' =
      ∑ j ∈ Finset.range (M+1), (pairMatrix F M z j).toBilin'.compl₁₂ old old := by
  rw [marginal_old_matrix]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  exact (old_old _ v w).symm

/-- Exact balanced marginal closure for the paper's raw integer matrices. -/
theorem marginal_removal_onePositive
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ) (hM : 2 ≤ M)
    (hsig : ∀ j ≤ M, OnePositiveDirection (integerRemovalMatrix F (profile z j (M-j))).toBilin')
    (hpos : ∀ j, 0 < j → j < M → 0 < F (profile z (j-1) (M-1-j))) :
    OnePositiveDirection (integerRemovalMatrix (marginal F M) z).toBilin' := by
  rw [marginal_old_block]
  apply balancedPair_sum_onePositive M hM
    (fun j => (pairMatrix F M z j).toBilin') old
    (Pi.single (.inr false) 1) (Pi.single (.inr true) 1) (cross F M z) (innerWeight F M z)
  · intro j _ x y
    exact (matrix_bilin_symm _ (integerRemoval_symm _ _)).eq x y
  · exact hsig
  · simp [innerWeight]
  · simp [innerWeight]
  · simp [innerWeight]
  · intro j hj0 hjM; simp [innerWeight,hj0,hjM,hpos j hj0 hjM]
  · simp [cross]
  · simp [cross]
  · intro j hj; simpa using pairMatrix_aa F M z j hj
  · intro j hj; simpa using pairMatrix_bb F M z j hj
  · intro j hj; simpa using pairMatrix_ab F M z j hj
  · exact cross_a F M z
  · exact cross_b F M z

/-- Equality-softening limits preserve the actual raw integer signature.
Only the finitely many displayed matrix entries are used. -/
theorem removal_signature_limit {K : Type*} {l : Filter K} [l.NeBot]
    (F : K → (I → ℕ) → ℝ) (f : (I → ℕ) → ℝ) (z : I → ℕ)
    (hlim : ∀ n, Filter.Tendsto (fun t => F t n) l (nhds (f n)))
    (hsig : ∀ᶠ t in l, OnePositiveDirection (integerRemovalMatrix (F t) z).toBilin') :
    OnePositiveDirection (integerRemovalMatrix f z).toBilin' := by
  apply (BinaryContraction.signature_iff _ (matrix_bilin_symm _ (integerRemoval_symm _ _))).mpr
  apply onePositive_of_tendsto (l := l) (fun t => integerRemovalMatrix (F t) z) (integerRemovalMatrix f z)
  · intro i j
    by_cases h : ValidPair z i j
    · simpa only [integerRemovalMatrix,h,ite_true] using hlim (removeTwo z i j)
    · simpa only [integerRemovalMatrix,h,ite_false] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : K => (0:ℝ)) l (nhds 0))
  · intro t
    exact integerRemoval_symm _ _
  · filter_upwards [hsig] with t ht
    exact (BinaryContraction.signature_iff _ (matrix_bilin_symm _ (integerRemoval_symm _ _))).mp ht

end ContingencyTables.IntegerMarginal

end OAI
