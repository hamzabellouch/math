import OAI.Analysis.HyperbolicCones.MatrixComplex
import OAI.Analysis.HyperbolicCones.FormPositive

namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Matrix

universe u

namespace Paper256

theorem qMatrix_transpose {R : Type u} [CommRing R] (y : Fin 3 → R) :
    (qMatrix y)ᵀ = qMatrix y := by
  ext i j
  by_cases h : i = j
  · subst j; rfl
  · simp [qMatrix, h, Ne.symm h, mul_comm]

theorem phi_transpose {R : Type u} [CommRing R] (y : Fin 3 → R) (X : Mat 4 R) :
    phi y Xᵀ = (phi y X)ᵀ := by
  have hQ (i j : Fin 3) : qMatrix y j i = qMatrix y i j :=
    congrFun (congrFun (qMatrix_transpose y) i) j
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  · change Matrix.trace (qMatrix y * (X.submatrix Fin.succ Fin.succ)ᵀ) =
      Matrix.trace (qMatrix y * X.submatrix Fin.succ Fin.succ)
    conv_lhs => rw [← qMatrix_transpose y]
    rw [← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm]
  · simp only [phi, Fin.cases_zero, Fin.cases_succ, Matrix.transpose_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hQ]
    ring
  · simp only [phi, Fin.cases_zero, Fin.cases_succ, Matrix.transpose_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hQ]
    ring
  · simp only [phi, Fin.cases_succ, Matrix.transpose_apply]
    rw [hQ]

theorem phi_conjTranspose (y : Fin 3 → ℝ) (X : Mat 4 ℂ) :
    (phi (fun i => (y i : ℂ)) X)ᴴ = phi (fun i => (y i : ℂ)) Xᴴ := by
  change ((phi (fun i => (y i : ℂ)) X)ᵀ).map (starRingEnd ℂ) = _
  rw [← phi_transpose, phi_map]
  have hy : (fun i => (starRingEnd ℂ) (y i : ℂ)) = (fun i => (y i : ℂ)) :=
    funext fun i => Complex.conj_ofReal (y i)
  rw [hy]
  rfl

theorem phi_complex_rank_one (y : Fin 3 → ℝ) (u v : Fin 4 → ℂ) :
    dotProduct (star u)
        (phi (fun i => (y i : ℂ)) (vecMulVec v (star v)) *ᵥ u) =
      dotProduct (star (fun i : Fin 3 => v 0 * u i.succ - u 0 * v i.succ))
        (qMatrix (fun i => (y i : ℂ)) *ᵥ
          (fun i : Fin 3 => v 0 * u i.succ - u 0 * v i.succ)) := by
  simp [dotProduct, mulVec, phi, qMatrix, Matrix.trace, Matrix.mul_apply,
    Matrix.submatrix, vecMulVec, Fin.sum_univ_succ]
  ring

theorem phi_complex_outer_posSemidef (y : Fin 3 → ℝ) (v : Fin 4 → ℂ) :
    (phi (fun i => (y i : ℂ)) (vecMulVec v (star v))).PosSemidef := by
  have hq : (qMatrix (fun i => (y i : ℂ))).PosSemidef := by
    have h := posSemidef_complexify (qMatrix y) (qMatrix_posSemidef y)
    change ((qMatrix y).map (algebraMap ℝ ℂ)).PosSemidef at h
    rw [qMatrix_map] at h
    exact h
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · show (phi (fun i => (y i : ℂ)) (vecMulVec v (star v)))ᴴ = _
    rw [phi_conjTranspose, (posSemidef_vecMulVec_self_star v).isHermitian.eq]
  · intro u
    rw [phi_complex_rank_one]
    exact hq.dotProduct_mulVec_nonneg _

theorem phi_complex_posSemidef (y : Fin 3 → ℝ) (X : Mat 4 ℂ) (hX : X.PosSemidef) :
    (phi (fun i => (y i : ℂ)) X).PosSemidef := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  have hx : X = ∑ i, vecMulVec (star (B i)) (B i) := by
    rw [hB]
    ext i j
    simp [Matrix.mul_apply, Matrix.sum_apply, vecMulVec]
  rw [hx]
  change ((phiLinear (fun i => (y i : ℂ))) (∑ i, vecMulVec (star (B i)) (B i))).PosSemidef
  rw [map_sum]
  apply Matrix.posSemidef_sum
  intro i _
  change (phi (fun i => (y i : ℂ)) (vecMulVec (star (B i)) (B i))).PosSemidef
  simpa only [star_star] using phi_complex_outer_posSemidef y (star (B i))

end Paper256

end

end OAI
