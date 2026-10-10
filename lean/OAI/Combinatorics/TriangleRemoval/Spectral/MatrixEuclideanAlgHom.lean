import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.IncidenceDegree
import OAI.Combinatorics.TriangleRemoval.Stability.Volterra
import OAI.Combinatorics.TriangleRemoval.Spectral.MatrixExpL2Bound

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave

noncomputable def matrixEuclideanAlgHom {I : Type*} [Fintype I] [DecidableEq I] :
    Matrix I I ℝ →ₐ[ℝ] (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) :=
  (Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ)).toAlgEquiv.toAlgHom

open scoped Matrix.Norms.L2Operator in

theorem euclidean_posSemidef_exp_bound {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℝ) (hP : P.PosSemidef) (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((-s) • matrixEuclideanAlgHom P)‖ ≤ 1 := by
  have hF : Continuous (matrixEuclideanAlgHom (I := I)) :=
    (matrixEuclideanAlgHom (I := I)).toLinearMap.continuous_of_finiteDimensional
  rw [← map_smul,← continuous_algHom_map_exp (matrixEuclideanAlgHom (I := I)) hF]
  exact matrix_posSemidef_exp_l2_le_one P hP s hs

open scoped Matrix.Norms.L2Operator in

theorem euclidean_perturbed_exp_bound {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (P R : Matrix I I ℝ) (hP : P.PosSemidef) (hR : IsSelfAdjoint R)
    (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((-s) • (matrixEuclideanAlgHom P + matrixEuclideanAlgHom R))‖ ≤
      Real.exp (s * ‖matrixEuclideanAlgHom R‖) := by
  have hF : Continuous (matrixEuclideanAlgHom (I := I)) :=
    (matrixEuclideanAlgHom (I := I)).toLinearMap.continuous_of_finiteDimensional
  rw [← map_add,← map_smul,← continuous_algHom_map_exp (matrixEuclideanAlgHom (I := I)) hF]
  exact matrix_perturbed_exp_l2_bound P R hP hR s hs

open scoped Matrix.Norms.Operator in

theorem matrix_infty_le_sqrt_card_euclidean {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) : ‖A‖ ≤ Real.sqrt (Fintype.card I) * ‖matrixEuclideanAlgHom A‖ := by
  apply matrix_norm_le_of_row_abs_sum_le _ _ (by positivity)
  intro i
  let v : EuclideanSpace ℝ I := WithLp.toLp 2 (fun j => if 0 ≤ A i j then 1 else -1)
  have hv : ‖v‖ = Real.sqrt (Fintype.card I) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    calc
      _ = ∑ _j : I, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [v]
        split_ifs <;> norm_num
      _ = _ := by simp
  have heq : (matrixEuclideanAlgHom A v).ofLp i = ∑ j, |A i j| := by
    change (Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) A v).ofLp i = _
    simp only [Matrix.ofLp_toEuclideanCLM,v,Matrix.mulVec,dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : 0 ≤ A i j
    · simp [h,abs_of_nonneg h]
    · simp [h,abs_of_neg (lt_of_not_ge h)]
  have hp := (PiLp.norm_apply_le (matrixEuclideanAlgHom A v) i).trans
    ((matrixEuclideanAlgHom A).le_opNorm v)
  rw [heq,Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _),hv] at hp
  simpa only [mul_comm] using hp

end SharpTerminalLeave

end

end OAI
