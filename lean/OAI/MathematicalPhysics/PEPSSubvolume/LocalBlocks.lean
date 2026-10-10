import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators

namespace OAI

/-! Local matrix-unit blocks with operator norm bounds. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.LocalBlocks
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def column (i : α) : Matrix (α×β) β ℂ :=
  fun x y => if x.1=i then (1:Matrix β β ℂ) x.2 y else 0

def block (H : Matrix (α×β) (α×β) ℂ) (i j : α) : Matrix β β ℂ :=
  fun x y => H (i,x) (j,y)

lemma column_gram (i : α) : (column (β := β) i).conjTranspose * column (β := β) i = 1 := by
  ext x y
  simp [column,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
    Matrix.one_apply,eq_comm]

lemma column_norm_le (i : α) : ‖column (β := β) i‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self (column (β := β) i)
  rw [column_gram] at h
  have h1 : ‖(1:Matrix β β ℂ)‖ ≤ 1 := by
    rw [← diagonal_one,l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun _ => by simp)
  nlinarith [norm_nonneg (column (β := β) i)]

lemma block_eq (H : Matrix (α×β) (α×β) ℂ) (i j : α) :
    block H i j = (column (β := β) i).conjTranspose * H * column (β := β) j := by
  ext x y
  simp [block,column,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
    Matrix.one_apply,apply_ite]

lemma block_norm_le (H : Matrix (α×β) (α×β) ℂ) (i j : α) :
    ‖block H i j‖ ≤ ‖H‖ := by
  rw [block_eq]
  calc
    _ ≤ ‖(column (β := β) i).conjTranspose‖ * ‖H‖ * ‖column (β := β) j‖ :=
      (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1 * ‖H‖ * 1 := by
      rw [l2_opNorm_conjTranspose]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (column_norm_le i) (norm_nonneg H))
        (column_norm_le j) (norm_nonneg _) (by positivity)
    _ = _ := by ring

omit [Fintype β] [DecidableEq β] in
lemma block_decomposition (H : Matrix (α×β) (α×β) ℂ) :
    H = ∑ i, ∑ j, Matrix.kronecker (Matrix.single i j (1:ℂ)) (block H i j) := by
  ext x y
  simp [Matrix.sum_apply,Matrix.kronecker,Matrix.kroneckerMap,Matrix.single_apply,block,ite_and]

lemma single_norm_le (i j : α) : ‖(Matrix.single i j (1:ℂ):Matrix α α ℂ)‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self (Matrix.single i j (1:ℂ):Matrix α α ℂ)
  have he : (Matrix.single i j (1:ℂ):Matrix α α ℂ).conjTranspose * Matrix.single i j 1 =
      diagonal (Pi.single j (1:ℂ)) := by
    simp only [conjTranspose_single,star_one,single_mul_single_same,one_mul]
    ext x y
    by_cases hx : x=j <;> by_cases hy : y=j <;>
      simp_all [Matrix.single_apply,diagonal_apply,eq_comm]

  rw [he,l2_opNorm_diagonal] at h
  have hn : ‖(Pi.single j (1:ℂ) : α → ℂ)‖ ≤ 1 := by
    apply pi_norm_le_iff_of_nonneg zero_le_one |>.mpr
    intro x
    by_cases hx : x=j <;> simp [hx]
  nlinarith [norm_nonneg (Matrix.single i j (1:ℂ):Matrix α α ℂ)]

lemma decomposition_cost (H : Matrix (α×β) (α×β) ℂ) :
    (∑ i, ∑ j, ‖(Matrix.single i j (1:ℂ):Matrix α α ℂ)‖ * ‖block H i j‖) ≤
      (Fintype.card α : ℝ)^2 * ‖H‖ := by
  calc
    _ ≤ ∑ i : α, ∑ j : α, ‖H‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact (mul_le_mul (single_norm_le i j) (block_norm_le H i j) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by simp; ring

end PolynomialPEPS.Subvolume.LocalBlocks

namespace PolynomialPEPS.Subvolume.LocalBlocks
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def reindexStarAlgEquiv (e : α ≃ β) : Matrix α α ℂ ≃⋆ₐ[ℂ] Matrix β β ℂ :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ e) (fun A =>
    (Matrix.conjTranspose_reindex e e A).symm)

lemma norm_reindex (e : α ≃ β) (A : Matrix α α ℂ) :
    ‖Matrix.reindex e e A‖ = ‖A‖ :=
  NonUnitalStarAlgHom.norm_map (reindexStarAlgEquiv e) (reindexStarAlgEquiv e).injective A

end PolynomialPEPS.Subvolume.LocalBlocks

end

end OAI
