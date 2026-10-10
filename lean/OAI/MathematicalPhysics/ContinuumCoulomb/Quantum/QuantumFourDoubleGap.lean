import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourCross
import Mathlib.Analysis.Matrix.Order

namespace OAI

/-! The full two-block penalty has a gap above its four-dimensional code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace Classical ComplexOrder

theorem qmaFourGap_posSemidef :
    (qmaFourPenalty-(4:ℂ) • (1-qmaFourProjection)).PosSemidef := by
  rw [qmaFourGap_complex,qmaFourSymmetricComplex_factor]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro k
  apply Complex.zero_le_real.mpr
  fin_cases k <;> norm_num [qmaFourSymmetricWeights]

theorem qmaFourComplement_posSemidef :
    (1-qmaFourProjection).PosSemidef := by
  have hP : qmaFourProjection*qmaFourProjection = qmaFourProjection := by
    rw [← qmaFourEncoding_projector]
    calc
      _ = qmaFourEncoding*(qmaFourEncoding.conjTranspose*qmaFourEncoding)*
          qmaFourEncoding.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [qmaFourEncoding_gram,Matrix.mul_one]
  have hstar : qmaFourProjection.conjTranspose = qmaFourProjection := by
    rw [← qmaFourEncoding_projector,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  have he : (1-qmaFourProjection).conjTranspose*(1-qmaFourProjection) =
      1-qmaFourProjection := by
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hstar]
    noncomm_ring [hP]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem qmaFourDouble_projector :
    qmaFourDoubleEncoding*qmaFourDoubleEncoding.conjTranspose =
      qmaFourProjection ⊗ₖ qmaFourProjection := by
  rw [qmaFourDoubleEncoding,Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,
    qmaFourEncoding_projector]

theorem qmaFourDoubleGap_posSemidef :
    (qmaFourDoublePenalty-(4:ℂ) • (1-qmaFourProjection ⊗ₖ qmaFourProjection)).PosSemidef := by
  have he : qmaFourDoublePenalty-(4:ℂ) • (1-qmaFourProjection ⊗ₖ qmaFourProjection) =
      (qmaFourPenalty-(4:ℂ) • (1-qmaFourProjection)) ⊗ₖ (1 : Matrix (Fin 16) (Fin 16) ℂ)+
      (1 : Matrix (Fin 16) (Fin 16) ℂ) ⊗ₖ (qmaFourPenalty-(4:ℂ) • (1-qmaFourProjection))+
      (4:ℂ) • ((1-qmaFourProjection) ⊗ₖ (1-qmaFourProjection)) := by
    ext s t
    rcases s with ⟨s₁,s₂⟩
    rcases t with ⟨t₁,t₂⟩
    by_cases h₁ : s₁ = t₁ <;> by_cases h₂ : s₂ = t₂ <;>
      simp [qmaFourDoublePenalty,Matrix.kroneckerMap_apply,h₁,h₂,Prod.ext_iff] <;> ring
  rw [he]
  exact ((qmaFourGap_posSemidef.kronecker Matrix.PosSemidef.one).add
    (Matrix.PosSemidef.one.kronecker qmaFourGap_posSemidef)).add
      ((qmaFourComplement_posSemidef.kronecker qmaFourComplement_posSemidef).smul (by norm_num))

theorem qmaFourDouble_complement_gap (x : EuclideanSpace ℂ (Fin 16 × Fin 16))
    (hx : qmaFourDoubleEncoding.conjTranspose *ᵥ (fun i => x i) = 0) :
    4*‖x‖^2 ≤ qmaQuadratic qmaFourDoublePenalty (fun i => x i) := by
  have hp : (qmaFourProjection ⊗ₖ qmaFourProjection) *ᵥ (fun i => x i) = 0 := by
    rw [← qmaFourDouble_projector,← Matrix.mulVec_mulVec,hx,Matrix.mulVec_zero]
  have hzero : qmaQuadratic (qmaFourProjection ⊗ₖ qmaFourProjection) (fun i => x i) = 0 := by
    simp [qmaQuadratic,hp]
  have hone : qmaQuadratic (1 : Matrix (Fin 16 × Fin 16) (Fin 16 × Fin 16) ℂ)
      (fun i => x i) = ‖x‖^2 := by
    rw [qmaQuadratic_operator,qmaMatrixOperator_square,spinMatrixOperator_one,one_apply_eq_self,
      real_inner_self_eq_norm_sq]
  have h := (Complex.nonneg_iff.mp
    (qmaFourDoubleGap_posSemidef.dotProduct_mulVec_nonneg (fun i => x i))).1
  change 0 ≤ qmaQuadratic _ (fun i => x i) at h
  rw [qmaQuadratic_sub] at h
  have hs : qmaQuadratic ((4:ℂ) • (1-qmaFourProjection ⊗ₖ qmaFourProjection)) (fun i => x i) =
      4*qmaQuadratic (1-qmaFourProjection ⊗ₖ qmaFourProjection) (fun i => x i) := by
    simpa only [Complex.ofReal_ofNat] using
      qmaQuadratic_smul (1-qmaFourProjection ⊗ₖ qmaFourProjection) (4:ℝ) (fun i => x i)
  rw [hs,qmaQuadratic_sub,hzero,hone] at h
  linarith

end ContinuumCoulomb

end

end OAI
