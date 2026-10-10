import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootDiagonalCharts

namespace OAI

/-! # Diagonal coordinates on the transverse lower triangular slice

Column ratios are fixed by the diagonal action; the logarithms of the
absolute diagonal entries are translated linearly. These are the actual
transverse coordinates, before choosing any finite entropy approximation.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma upperRootTransverse_lowerTriangular {n : ℕ} (s : UpperRootTransverse n) :
    s.val.val.IsLowerTriangular := by
  intro i j hij
  have h := s.prop.1 (i,j)
    (by rw [completeRootChain_final]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩)
  exact h

lemma upperRootTransverse_diagonal_ne_zero {n : ℕ} (s : UpperRootTransverse n) (i : Fin n) :
    s.val.val i i ≠ 0 := by
  have hprod : ∏ j, s.val.val j j=1 :=
    (Matrix.det_of_isLowerTriangular s.val.val (upperRootTransverse_lowerTriangular s)).symm.trans
      s.val.prop
  have hn : ∏ j, s.val.val j j ≠ 0 := by rw [hprod]; exact one_ne_zero
  exact (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i)

def transverseColumnRatios {n : ℕ} (s : UpperRootTransverse n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => s.val.val i j/s.val.val j j

def transverseLogDiagonal {n : ℕ} (s : UpperRootTransverse n) : Fin n → ℝ :=
  fun i => Real.log |s.val.val i i|

lemma continuous_transverseColumnRatios (n : ℕ) :
    Continuous (@transverseColumnRatios n) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hentry (i j : Fin n) : Continuous (fun s : UpperRootTransverse n => s.val.val i j) := by
    fun_prop
  exact (hentry i j).div (hentry j j) (fun s => upperRootTransverse_diagonal_ne_zero s j)

lemma continuous_transverseLogDiagonal (n : ℕ) :
    Continuous (@transverseLogDiagonal n) := by
  apply continuous_pi
  intro i
  have hentry : Continuous (fun s : UpperRootTransverse n => s.val.val i i) := by
    fun_prop
  exact hentry.abs.log (fun s => abs_ne_zero.mpr (upperRootTransverse_diagonal_ne_zero s i))

lemma transverseColumnRatios_diagonal {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i=0) (t : ℝ) (s : UpperRootTransverse n) :
    transverseColumnRatios (upperRootTransverseDiagonal ell hell t s) =
      transverseColumnRatios s := by
  funext i j
  change (s.val*diagonalOneParameter ell hell t).val i j /
      (s.val*diagonalOneParameter ell hell t).val j j = _
  rw [mul_diagonalOneParameter_entry,mul_diagonalOneParameter_entry]
  exact mul_div_mul_right _ _ (Real.exp_ne_zero _)

lemma transverseLogDiagonal_diagonal {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i=0) (t : ℝ) (s : UpperRootTransverse n) :
    transverseLogDiagonal (upperRootTransverseDiagonal ell hell t s) =
      fun i => transverseLogDiagonal s i+ell i*t := by
  funext i
  change Real.log |(s.val*diagonalOneParameter ell hell t).val i i| = _
  rw [mul_diagonalOneParameter_entry,abs_mul,abs_of_pos (Real.exp_pos _),
    Real.log_mul (abs_ne_zero.mpr (upperRootTransverse_diagonal_ne_zero s i))
      (Real.exp_ne_zero _),Real.log_exp]
  rfl

lemma transverse_data_injective {n : ℕ} {s r : UpperRootTransverse n}
    (hrat : transverseColumnRatios s=transverseColumnRatios r)
    (hdiag : ∀ j, s.val.val j j=r.val.val j j) : s=r := by
  apply Subtype.ext
  apply Subtype.ext
  funext i j
  have h := congrFun (congrFun hrat i) j
  change s.val.val i j/s.val.val j j=r.val.val i j/r.val.val j j at h
  rw [hdiag j] at h
  exact (div_left_inj' (upperRootTransverse_diagonal_ne_zero r j)).mp h

end DukePrimeDegree

end

end OAI
