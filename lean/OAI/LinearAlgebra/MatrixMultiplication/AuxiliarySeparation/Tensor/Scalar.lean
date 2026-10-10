import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Semiring
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-!
# Natural numbers and rank in the tensor semiring

The natural number `r` is the class of the diagonal scalar tensor with `r`
terms.  Consequently, comparison with `r` in the restriction order is exactly
the existence of a rank decomposition with `r` terms.
-/

noncomputable section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

/-- Splitting the diagonal index set splits its scalar tensor into two blocks. -/
theorem scalarTensor_add_reindex (m n : ℕ) :
    Tensor.pullback (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
      finSumFinEquiv finSumFinEquiv (scalarTensor (m + n)) =
      sumTensor (scalarTensor m) (scalarTensor n) := by
  funext x y z
  simp only [Tensor.pullback, scalarTensor,
    (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).injective.eq_iff]
  cases x <;> cases y <;> cases z <;> simp [sumTensor, scalarTensor]

/-- A diagonal scalar tensor has its evident decomposition into simple terms. -/
theorem scalarTensor_rankAtMost (r : ℕ) : Tensor.RankAtMost (scalarTensor r) r := by
  classical
  refine ⟨(fun i x => if x = i then 1 else 0),
    (fun i y => if y = i then 1 else 0), (fun i z => if z = i then 1 else 0), ?_⟩
  funext x y z
  simp [scalarTensor, Tensor.rankOne, mul_ite, ite_and]
  split_ifs <;> simp_all

/-- The diagonal flattening also gives the matching lower bound. -/
@[simp] theorem exactRank_scalarTensor (r : ℕ) : exactRank (scalarTensor r) = r := by
  apply le_antisymm (exactRank_le (scalarTensor_rankAtMost r))
  have h := (exactRank_spec (scalarTensor r)).card_le_of_identity id id id
    (by intro i j; simp [scalarTensor])
  simpa only [Fintype.card_fin] using h

namespace TensorSemiring

/-- Addition of the diagonal index sets is semiring addition. -/
theorem classOf_scalarTensor_add (m n : ℕ) :
    classOf (scalarTensor (m + n)) =
      classOf (scalarTensor m) + classOf (scalarTensor n) := by
  have h := classOf_eq_of_reindex _ _ _ (scalarTensor_add_reindex m n)
  exact h.symm.trans (classOf_sum _ _)

@[simp] theorem classOf_scalarTensor_zero :
    classOf (scalarTensor 0) = (0 : TensorClass) := by
  have h : scalarTensor 0 = 0 := by
    funext x
    exact Fin.elim0 x
  rw [h, classOf_zero]

@[simp] theorem classOf_scalarTensor_one :
    classOf (scalarTensor 1) = (1 : TensorClass) := by
  change classOf (scalarTensor 1) = classOf (fun (_ _ _ : PUnit.{1}) => (1 : ℂ))
  apply classOf_eq_of_reindex (Equiv.equivPUnit (Fin 1))
    (Equiv.equivPUnit (Fin 1)) (Equiv.equivPUnit (Fin 1))
  funext x y z
  simp [Tensor.pullback, scalarTensor, Subsingleton.elim x y, Subsingleton.elim y z]

/-- Natural numbers in the quotient semiring have their intended tensor meaning. -/
@[simp] theorem classOf_scalarTensor (r : ℕ) :
    classOf (scalarTensor r) = (r : TensorClass) := by
  induction r with
  | zero => exact classOf_scalarTensor_zero
  | succ r ih =>
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ,
        classOf_scalarTensor_one, ih] using
        classOf_scalarTensor_add r 1

/-- Exact rank decompositions are precisely restrictions of diagonal tensors. -/
theorem rankAtMost_iff_isRestriction_scalarTensor
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (r : ℕ) :
    Tensor.RankAtMost T r ↔ IsRestriction T (scalarTensor r) := by
  constructor
  · rintro ⟨a, b, c, h⟩
    refine ⟨(fun x i => a i x), (fun y i => b i y), (fun z i => c i z), ?_⟩
    apply h.trans
    funext x y z
    simp [Tensor.restrict, scalarTensor, Tensor.rankOne, mul_ite, ite_and]
  · rintro ⟨A, B, C, rfl⟩
    exact (scalarTensor_rankAtMost r).restrict A B C

/-- The restriction order below a natural number is exactly the usual rank bound. -/
theorem classOf_le_nat_iff_rankAtMost
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (r : ℕ) :
    classOf T ≤ (r : TensorClass) ↔ Tensor.RankAtMost T r := by
  rw [← classOf_scalarTensor r, classOf_le_iff]
  exact (rankAtMost_iff_isRestriction_scalarTensor T r).symm

/-- Rank takes its usual value on natural numbers in the tensor semiring. -/
@[simp] theorem rank_natCast (r : ℕ) : rank (r : TensorClass) = r := by
  rw [← classOf_scalarTensor r, rank_classOf, exactRank_scalarTensor]

/-- The rank is a natural-number upper bound in the restriction order. -/
theorem le_rank (T : TensorClass) : T ≤ (rank T : TensorClass) := by
  induction T using Quotient.inductionOn with
  | h T =>
    change tensorClass T ≤ (exactRank T.coeff : TensorClass)
    rw [← classOf_coeff T]
    exact (classOf_le_nat_iff_rankAtMost T.coeff (exactRank T.coeff)).mpr
      (exactRank_spec T.coeff)

/-- The tensor restriction order induces the usual order on natural numbers. -/
@[simp] theorem natCast_le_natCast_iff (m n : ℕ) :
    (m : TensorClass) ≤ (n : TensorClass) ↔ m ≤ n := by
  constructor
  · intro h
    simpa only [rank_natCast] using rank_mono h
  · intro h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.cast_add]
    simpa only [add_zero] using add_mono (le_refl (m : TensorClass)) (zero_le (k : TensorClass))

/-- A natural multiple of any nonzero tensor contains any prescribed tensor
by restriction. -/
theorem le_nat_mul_of_ne_zero (T S : TensorClass) (hS : S ≠ 0) :
    T ≤ (rank T : TensorClass) * S := by
  apply (le_rank T).trans
  simpa only [mul_one] using
    mul_mono (le_refl (rank T : TensorClass)) (one_le_of_ne_zero hS)

end TensorSemiring
end MatrixMultiplication.AuxiliarySeparation

end

end OAI
