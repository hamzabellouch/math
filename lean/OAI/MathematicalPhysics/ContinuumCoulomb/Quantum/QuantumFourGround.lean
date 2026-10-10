import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourLogical

namespace OAI

/-! The four-spin penalty vanishes exactly on the encoded qubit. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical

theorem qmaFourLogical_sum :
    qmaFourLogical 0 1+qmaFourLogical 0 2+qmaFourLogical 0 3+
      qmaFourLogical 1 2+qmaFourLogical 1 3+qmaFourLogical 2 3 =
        (-6:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [qmaFourLogical] <;> ring

theorem qmaFourPenalty_exchange : qmaFourPenalty =
    qmaFourExchange 0 1+qmaFourExchange 0 2+qmaFourExchange 0 3+
      qmaFourExchange 1 2+qmaFourExchange 1 3+qmaFourExchange 2 3+
        (6:ℂ) • (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
  ext s t
  by_cases h : s = t
  all_goals
    simp [qmaFourPenalty,qmaFourPenaltyRational,qmaFourExchange,Matrix.map_apply,h]

theorem qmaFourPenalty_encoding : qmaFourPenalty*qmaFourEncoding = 0 := by
  rw [qmaFourPenalty_exchange]
  simp only [Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul]
  rw [qmaFourEncoding_action 0 1 (by decide),qmaFourEncoding_action 0 2 (by decide),
    qmaFourEncoding_action 0 3 (by decide),qmaFourEncoding_action 1 2 (by decide),
    qmaFourEncoding_action 1 3 (by decide),qmaFourEncoding_action 2 3 (by decide)]
  rw [← Matrix.mul_add,← Matrix.mul_add,← Matrix.mul_add,← Matrix.mul_add,
    ← Matrix.mul_add,qmaFourLogical_sum,Matrix.mul_smul,Matrix.mul_one]
  simp

theorem qmaFourPenalty_range (x : Fin 2 → ℂ) :
    qmaFourPenalty *ᵥ (qmaFourEncoding *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec,qmaFourPenalty_encoding,Matrix.zero_mulVec]

theorem qmaFourPenalty_kernel (x : EuclideanSpace ℂ (Fin 16))
    (hx : qmaFourPenalty *ᵥ (fun i => x i) = 0) :
    qmaFourProjection *ᵥ (fun i => x i) = (fun i => x i) := by
  have hq : qmaQuadratic qmaFourPenalty (fun i => x i) = 0 := by
    simp [qmaQuadratic,hx]
  have hg := qmaFourGap_form x
  rw [hq] at hg
  have hP := qmaFourEncoding_projector
  have hgram := qmaFourEncoding_gram
  have hproj : qmaFourProjection*qmaFourProjection = qmaFourProjection := by
    rw [← hP]
    calc
      _ = qmaFourEncoding*(qmaFourEncoding.conjTranspose*qmaFourEncoding)*
          qmaFourEncoding.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hgram,Matrix.mul_one]
  have hstar : qmaFourProjection.conjTranspose = qmaFourProjection := by
    rw [← hP,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  let y : EuclideanSpace ℂ (Fin 16) :=
    WithLp.toLp 2 ((fun i => x i)-qmaFourProjection *ᵥ (fun i => x i))
  have hyop : qmaMatrixOperator (1-qmaFourProjection) x = y := by
    ext i
    simp [qmaMatrixOperator_apply,y,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib,
      Matrix.one_apply,Matrix.mulVec,dotProduct]
  have hy : ‖y‖^2 = qmaQuadratic (1-qmaFourProjection) (fun i => x i) := by
    rw [← real_inner_self_eq_norm_sq,qmaEuclidean_real_inner,← hyop]
    rw [← ContinuousLinearMap.adjoint_inner_right]
    rw [← qmaMatrixOperator_star]
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hstar]
    rw [← ContinuousLinearMap.comp_apply,← qmaMatrixOperator_mul]
    have he : (1-qmaFourProjection)*(1-qmaFourProjection) = 1-qmaFourProjection := by
      noncomm_ring [hproj]
    rw [he]
    rw [← qmaEuclidean_real_inner]
    exact (qmaQuadratic_operator (1-qmaFourProjection) x).symm
  have hn : ‖y‖ = 0 := by
    rw [qmaQuadratic_sub] at hy
    have hnon := sq_nonneg ‖y‖
    nlinarith
  have hz := norm_eq_zero.mp hn
  have hv : (fun i => x i)-qmaFourProjection *ᵥ (fun i => x i) = 0 := by
    simpa only [y,WithLp.toLp_eq_zero] using hz
  exact (sub_eq_zero.mp hv).symm

end ContinuumCoulomb

end

end OAI
