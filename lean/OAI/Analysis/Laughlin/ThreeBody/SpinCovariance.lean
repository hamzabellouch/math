import OAI.Analysis.Laughlin.Spin.TripleLadderIntertwining
import OAI.Analysis.Laughlin.ThreeBody.GramSlice

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

noncomputable def swapCompression (Q : ℕ) : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ :=
  (tripleInclusion Q)ᵀ * swap23Matrix Q * tripleInclusion Q

noncomputable def threeGram (Q : ℕ) : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ :=
  1 - (2 : ℝ) • swapCompression Q

theorem swapCompression_raising (Q : ℕ) (hQ : 0 < Q) :
    swapCompression Q * totalRaise (2*Q-2) Q = totalRaise (2*Q-2) Q * swapCompression Q := by
  unfold swapCompression
  calc
    _ = (tripleInclusion Q)ᵀ * swap23Matrix Q *
      (tripleInclusion Q * totalRaise (2*Q-2) Q) := by simp only [Matrix.mul_assoc]
    _ = (tripleInclusion Q)ᵀ * swap23Matrix Q *
      (tripleRaise Q * tripleInclusion Q) := by rw [tripleInclusion_raising Q hQ]
    _ = (tripleInclusion Q)ᵀ * (swap23Matrix Q * tripleRaise Q) * tripleInclusion Q := by
      simp only [Matrix.mul_assoc]
    _ = (tripleInclusion Q)ᵀ * (tripleRaise Q * swap23Matrix Q) * tripleInclusion Q := by
      rw [swap23_raising]
    _ = ((tripleInclusion Q)ᵀ * tripleRaise Q) * swap23Matrix Q * tripleInclusion Q := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [tripleInclusion_transpose_raising Q hQ]; simp only [Matrix.mul_assoc]

theorem threeGram_raising (Q : ℕ) (hQ : 0 < Q) :
    threeGram Q * totalRaise (2*Q-2) Q = totalRaise (2*Q-2) Q * threeGram Q := by
  simp only [threeGram,Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,
    Matrix.smul_mul,Matrix.mul_smul,swapCompression_raising Q hQ]

theorem swapCompression_entry (Q : ℕ) (a b : PairOrbitalIndex Q) :
    swapCompression Q a b = ∑ t : Orbital Q,
      pairCoefficient Q a.1.val b.2 t * pairCoefficient Q b.1.val a.2 t := by
  have he (i : TripleIndex Q) :
      ((tripleInclusion Q)ᵀ * swap23Matrix Q) a i = tripleInclusion Q (swap23 i) a := by
    have hi (k : TripleIndex Q) : swap23 k=i ↔ k=swap23 i := by
      constructor
      · intro h; simpa using congrArg swap23 h
      · intro h; rw [h,swap23_involutive]
    simp [Matrix.mul_apply,swap23Matrix,hi,Matrix.transpose_apply]
  unfold swapCompression
  rw [Matrix.mul_apply]
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [tripleInclusion,pairInclusion,Matrix.kroneckerMap,
    Matrix.of_apply,Matrix.one_apply,swap23]
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro t ht
  rw [pairCoefficient_swap Q a.1.val t b.2,pairCoefficient_swap Q b.1.val t a.2]
  ring

theorem threeGram_entry (Q : ℕ) (a b : PairOrbitalIndex Q) :
    threeGram Q a b = (if a=b then 1 else 0) - 2*∑ t : Orbital Q,
      pairCoefficient Q a.1.val b.2 t * pairCoefficient Q b.1.val a.2 t := by
  simp only [threeGram,Matrix.sub_apply,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,
    swapCompression_entry]

theorem threeGram_physical (Q : ℕ) (hQ : 2 ≤ Q) (a b : PairOrbitalIndex Q) :
    (threeGram Q a b : ℂ) =
      Fock.occupationInner Q (Fock.threeBodyColumn Q a.1.val a.2)
        (Fock.threeBodyColumn Q b.1.val b.2) := by
  rw [threeGram_entry,Fock.threeBodyColumn_gram Q a.1.val b.1.val hQ (by omega)]
  push_cast
  congr 1
  by_cases ha : a.1=b.1 <;> by_cases hb : a.2=b.2 <;>
    simp [Prod.ext_iff,ha,hb]
  simp_all [Fin.ext_iff]

theorem threeGram_weight (Q : ℕ) (a b : PairOrbitalIndex Q)
    (h : a.1.val+a.2.val ≠ b.1.val+b.2.val) : threeGram Q a b = 0 := by
  have hab : a ≠ b := by intro he; apply h; rw [he]
  rw [threeGram_entry,ite_eq_right hab]
  have hz : (∑ t : Orbital Q, pairCoefficient Q a.1.val b.2 t *
      pairCoefficient Q b.1.val a.2 t) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    by_cases ha : b.2.val+t.val=a.1.val+1
    · have hb : a.2.val+t.val ≠ b.1.val+1 := by omega
      simp [pairCoefficient,hb]
    · simp [pairCoefficient,ha]
  rw [hz]; ring

end Laughlin.Spin

end OAI
