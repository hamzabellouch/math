import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourPositive

namespace OAI

/-! The rational projection is exactly the normalized singlet range. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical

theorem qmaFourNormalization_square : qmaFourNormalization*qmaFourNormalization.conjTranspose =
    (Matrix.diagonal ![(1/4:ℚ),1/12]).map (Rat.castHom ℂ) := by
  have hs0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsc : (Real.sqrt 3:ℂ) ≠ 0 := by exact_mod_cast hs0
  have hs : (Real.sqrt 3:ℂ)^2 = 3 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have htwo : (starRingEnd ℂ) (2:ℂ) = 2 := Complex.conj_ofReal 2
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourNormalization,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.map_apply,
      Matrix.diagonal_apply,Fin.sum_univ_two,Complex.star_def,htwo]
  field_simp
  rw [hs]
  norm_num

theorem qmaFourProjectionRational_factor :
    qmaFourRawEncoding*Matrix.diagonal ![(1/4:ℚ),1/12]*qmaFourRawEncoding.transpose =
      qmaFourProjectionRational := by
  ext s t
  simp [Matrix.mul_apply,Matrix.diagonal_apply,Matrix.transpose_apply,Fin.sum_univ_two,
    qmaFourRawEncoding,qmaFourProjectionRational]
  ring

theorem qmaFourEncoding_projector : qmaFourEncoding*qmaFourEncoding.conjTranspose = qmaFourProjection := by
  calc
    _ = qmaFourRawComplex*(qmaFourNormalization*qmaFourNormalization.conjTranspose)*
        qmaFourRawComplex.conjTranspose := by
      simp only [qmaFourEncoding,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = qmaFourProjection := by
      rw [qmaFourNormalization_square,qmaFourRawComplex_adjoint,qmaFourRawComplex,
        ← Matrix.map_mul,← Matrix.map_mul,qmaFourProjectionRational_factor]
      rfl

theorem qmaFour_complement_gap (x : EuclideanSpace ℂ (Fin 16))
    (hx : qmaFourEncoding.conjTranspose *ᵥ (fun i => x i) = 0) :
    4*‖x‖^2 ≤ qmaQuadratic qmaFourPenalty (fun i => x i) := by
  have hp : qmaFourProjection *ᵥ (fun i => x i) = 0 := by
    rw [← qmaFourEncoding_projector,← Matrix.mulVec_mulVec,hx,Matrix.mulVec_zero]
  have hzero : qmaQuadratic qmaFourProjection (fun i => x i) = 0 := by simp [qmaQuadratic,hp]
  have hone : qmaQuadratic (1 : Matrix (Fin 16) (Fin 16) ℂ) (fun i => x i) = ‖x‖^2 := by
    rw [qmaQuadratic_operator,qmaMatrixOperator_square,spinMatrixOperator_one,one_apply_eq_self,
      real_inner_self_eq_norm_sq]
  have h := qmaFourGap_form x
  rwa [hzero,sub_zero,hone] at h

end ContinuumCoulomb

end

end OAI
