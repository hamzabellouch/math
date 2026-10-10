import OAI.NumberTheory.DukePrimeDegree.Dynamics.TransverseStabilizerLimit

namespace OAI

/-!
# The actual centralizer of a singular diagonal

Equal weights determine the neutral blocks. The resulting concrete block
matrix subgroup is precisely the centralizer of any nonzero time of the
diagonal flow. No symmetry assertion about the measure's invariant-root
relation is used in this identification.
-/

noncomputable section
open Matrix Set
open scoped BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def weightBlockSetoid {n : ℕ} (ell : Fin n → ℝ) : Setoid (Fin n) where
  r i j := ell i = ell j
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

lemma matrix_commute_weight_diagonal_iff {n : ℕ}
    (ell : Fin n → ℝ) (t : ℝ) (ht : t ≠ 0)
    (V : Matrix (Fin n) (Fin n) ℝ) :
    Commute V (Matrix.diagonal (fun i => Real.exp (ell i * t))) ↔
      ∀ i j, ell i ≠ ell j → V i j = 0 := by
  constructor
  · intro h i j hij
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) h.eq
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    have hn : Real.exp (ell j * t) - Real.exp (ell i * t) ≠ 0 := by
      intro hh
      exact hij ((mul_right_cancel₀ ht
        (Real.exp_injective (sub_eq_zero.mp hh))).symm)
    have hz : V i j * (Real.exp (ell j * t) - Real.exp (ell i * t)) = 0 := by
      nlinarith [he]
    exact (mul_eq_zero.mp hz).resolve_right hn
  · intro h
    change V * Matrix.diagonal (fun i => Real.exp (ell i * t)) =
      Matrix.diagonal (fun i => Real.exp (ell i * t)) * V
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : ell i = ell j
    · rw [hij, mul_comm]
    · simp only [h i j hij, zero_mul, mul_zero]

theorem mem_weightBlockGroup_iff_commute_flow {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (t : ℝ) (ht : t ≠ 0) (g : G n) :
    g ∈ blockMatrixGroup (weightBlockSetoid ell) ↔
      Commute g (diagonalOneParameter ell hell t) := by
  have hmatrix : Commute g.val (diagonalOneParameter ell hell t).val ↔
      ∀ i j, ell i ≠ ell j → g.val i j = 0 :=
    matrix_commute_weight_diagonal_iff ell t ht g.val
  constructor
  · intro hg
    have hm : Commute g.val (diagonalOneParameter ell hell t).val :=
      hmatrix.mpr (fun i j hij => cross_zero_of_mem_blockMatrixGroup
        (weightBlockSetoid ell) g hg i j hij)
    exact Subtype.ext hm.eq
  · intro hg
    apply mem_blockMatrixGroup_of_cross_zero (weightBlockSetoid ell) g
    exact hmatrix.mp (congrArg Subtype.val hg.eq)

end DukePrimeDegree

end

end OAI
