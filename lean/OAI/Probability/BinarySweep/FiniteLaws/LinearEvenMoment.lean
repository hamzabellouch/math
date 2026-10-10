import Mathlib
import OAI.Probability.BinarySweep.Representations.IsotypicMoment
import OAI.Probability.BinarySweep.MatrixBounds.SchattenBasic

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open TraceHolder

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] [Fintype ι] [DecidableEq ι]

lemma trace_orthonormalMatrix (v : OrthonormalBasis ι ℂ V) (A : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ V A = Matrix.trace (LinearMap.toMatrixOrthonormal v A) :=
  LinearMap.trace_eq_matrix_trace ℂ v.toBasis A

lemma evenMoment_orthonormalMatrix (v : OrthonormalBasis ι ℂ V) (q : ℕ) (A : V →ₗ[ℂ] V) :
    evenMoment q A=matrixMoment q (LinearMap.toMatrixOrthonormal v A) := by
  unfold evenMoment matrixMoment
  rw [trace_orthonormalMatrix v]
  simp only [map_pow,map_mul,← LinearMap.star_eq_adjoint,map_star]

lemma evenMoment_nonneg (q : ℕ) (A : V →ₗ[ℂ] V) : 0≤evenMoment q A := by
  rw [evenMoment_orthonormalMatrix (stdOrthonormalBasis ℂ V)]
  exact matrixMoment_nonneg _ _

lemma evenMoment_adjoint (q : ℕ) (A : V →ₗ[ℂ] V) : evenMoment q A.adjoint=evenMoment q A := by
  rw [evenMoment_orthonormalMatrix (stdOrthonormalBasis ℂ V),
    evenMoment_orthonormalMatrix (stdOrthonormalBasis ℂ V)]
  rw [← LinearMap.star_eq_adjoint,map_star]
  exact matrixMoment_star q _

lemma evenMoment_smul (q : ℕ) (r : ℝ) (A : V →ₗ[ℂ] V) :
    evenMoment q (r • A)=r^(2*q)*evenMoment q A := by
  rw [evenMoment_orthonormalMatrix (stdOrthonormalBasis ℂ V),
    evenMoment_orthonormalMatrix (stdOrthonormalBasis ℂ V)]
  rw [← algebraMap_smul ℂ r A,map_smul]
  rw [algebraMap_smul ℂ r]
  exact matrixMoment_smul q r _

lemma evenMoment_unitary_left (q : ℕ) (U A : V →ₗ[ℂ] V) (hu : U.adjoint*U=1) :
    evenMoment q (U*A)=evenMoment q A := by
  unfold evenMoment
  rw [show (U*A).adjoint*(U*A)=A.adjoint*A by
    rw [← LinearMap.star_eq_adjoint,star_mul]; calc
      _ = A.adjoint*(U.adjoint*U)*A := by noncomm_ring
      _ = _ := by rw [hu,mul_one]]

lemma linear_trace_holder {q : ℕ} (hq : 0<q) (A : Fin (2*q) → V →ₗ[ℂ] V) :
    ‖LinearMap.trace ℂ V (List.ofFn A).prod‖ ≤
      ∏j, evenMoment q (A j)^(((2*q:ℕ):ℝ)⁻¹) := by
  let v := stdOrthonormalBasis ℂ V
  rw [trace_orthonormalMatrix v,map_list_prod,List.map_ofFn]
  simpa only [Function.comp_def,evenMoment_orthonormalMatrix v] using
    matrix_trace_holder hq (fun j => LinearMap.toMatrixOrthonormal v (A j))

end BinaryCoordinateSweeps.Irrep

end

end OAI
