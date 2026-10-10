import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTensorSucc

namespace OAI

/-! The actual many-block four-spin penalty has a uniform full-complement gap. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical ComplexOrder

theorem qmaFourProjection_star : qmaFourProjection.conjTranspose = qmaFourProjection := by
  rw [← qmaFourEncoding_projector,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]

theorem qmaFourProjection_square : qmaFourProjection*qmaFourProjection = qmaFourProjection := by
  rw [← qmaFourEncoding_projector]
  calc
    _ = qmaFourEncoding*(qmaFourEncoding.conjTranspose*qmaFourEncoding)*
        qmaFourEncoding.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [qmaFourEncoding_gram,Matrix.mul_one]

def qmaFourTensorEncoding (n : ℕ) : Matrix (Fin n → Fin 16) (Fin n → Fin 2) ℂ :=
  qmaTensorMatrix (fun _ => qmaFourEncoding)

def qmaFourTensorProjection (n : ℕ) : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  qmaTensorMatrix (fun _ => qmaFourProjection)

def qmaFourTensorPenalty (n : ℕ) : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  qmaTensorPenalty n qmaFourPenalty

theorem qmaFourTensorEncoding_gram (n : ℕ) :
    (qmaFourTensorEncoding n).conjTranspose*qmaFourTensorEncoding n = 1 :=
  qmaTensorMatrix_gram _ (fun _ => qmaFourEncoding_gram)

theorem qmaFourTensorEncoding_projector (n : ℕ) :
    qmaFourTensorEncoding n*(qmaFourTensorEncoding n).conjTranspose = qmaFourTensorProjection n := by
  rw [qmaFourTensorEncoding,qmaTensorMatrix_star,qmaTensorMatrix_mul]
  simp only [qmaFourEncoding_projector,qmaFourTensorProjection]

theorem qmaFourTensorComplement_posSemidef (n : ℕ) :
    (1-qmaFourTensorProjection n).PosSemidef :=
  qmaTensorMatrix_complement_posSemidef _ (fun _ => qmaFourProjection_star)
    (fun _ => qmaFourProjection_square)

theorem qmaFourTensorGap_posSemidef (n : ℕ) :
    (qmaFourTensorPenalty n-(4:ℂ) • (1-qmaFourTensorProjection n)).PosSemidef := by
  induction n with
  | zero =>
    have hP : qmaFourTensorProjection 0 = 1 := by
      ext s t
      simp [qmaFourTensorProjection,qmaTensorMatrix,Matrix.one_apply,Subsingleton.elim s t]
    simpa only [qmaFourTensorPenalty,qmaTensorPenalty,Fin.sum_univ_zero,hP,sub_self,smul_zero,sub_zero]
      using (Matrix.PosSemidef.zero : (0 : Matrix (Fin 0 → Fin 16) (Fin 0 → Fin 16) ℂ).PosSemidef)
  | succ n ih =>
    let P := qmaFourTensorProjection n
    let H := qmaFourTensorPenalty n
    have he : qmaFourTensorPenalty (n+1)-(4:ℂ) • (1-qmaFourTensorProjection (n+1)) =
        (qmaFourPenalty ⊗ₖ (1 : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)+
          (1 : Matrix (Fin 16) (Fin 16) ℂ) ⊗ₖ H-
            (4:ℂ) • (1-qmaFourProjection ⊗ₖ P)).submatrix
              (qmaTensorSuccEquiv (Fin 16) n) (qmaTensorSuccEquiv (Fin 16) n) := by
      rw [qmaFourTensorPenalty,qmaTensorPenalty_succ,qmaFourTensorProjection,qmaTensorMatrix_succ]
      simp only [Matrix.submatrix_sub,Matrix.submatrix_smul,Pi.sub_apply,Pi.smul_apply,
        Matrix.submatrix_one_equiv]
      rfl
    have hsplit : qmaFourPenalty ⊗ₖ (1 : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)+
          (1 : Matrix (Fin 16) (Fin 16) ℂ) ⊗ₖ H-(4:ℂ) • (1-qmaFourProjection ⊗ₖ P) =
        (qmaFourPenalty-(4:ℂ) • (1-qmaFourProjection)) ⊗ₖ (1 : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)+
          (1 : Matrix (Fin 16) (Fin 16) ℂ) ⊗ₖ (H-(4:ℂ) • (1-P))+
          (4:ℂ) • ((1-qmaFourProjection) ⊗ₖ (1-P)) := by
      ext s t
      rcases s with ⟨s₁,s₂⟩
      rcases t with ⟨t₁,t₂⟩
      by_cases h₁ : s₁ = t₁ <;> by_cases h₂ : s₂ = t₂ <;>
        simp [Matrix.kroneckerMap_apply,h₁,h₂,Prod.ext_iff] <;> ring
    rw [he,hsplit]
    apply Matrix.PosSemidef.submatrix
    exact ((qmaFourGap_posSemidef.kronecker Matrix.PosSemidef.one).add
      (Matrix.PosSemidef.one.kronecker ih)).add
        ((qmaFourComplement_posSemidef.kronecker (qmaFourTensorComplement_posSemidef n)).smul
          (by norm_num))

theorem qmaFourTensor_complement_gap (n : ℕ) (x : EuclideanSpace ℂ (Fin n → Fin 16))
    (hx : (qmaFourTensorEncoding n).conjTranspose *ᵥ (fun i => x i) = 0) :
    4*‖x‖^2 ≤ qmaQuadratic (qmaFourTensorPenalty n) (fun i => x i) := by
  have hp : qmaFourTensorProjection n *ᵥ (fun i => x i) = 0 := by
    rw [← qmaFourTensorEncoding_projector,← Matrix.mulVec_mulVec,hx,Matrix.mulVec_zero]
  have hzero : qmaQuadratic (qmaFourTensorProjection n) (fun i => x i) = 0 := by
    simp [qmaQuadratic,hp]
  have hone : qmaQuadratic (1 : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
      (fun i => x i) = ‖x‖^2 := by
    rw [qmaQuadratic_operator,qmaMatrixOperator_square,spinMatrixOperator_one,one_apply_eq_self,
      real_inner_self_eq_norm_sq]
  have h := (Complex.nonneg_iff.mp
    ((qmaFourTensorGap_posSemidef n).dotProduct_mulVec_nonneg (fun i => x i))).1
  change 0 ≤ qmaQuadratic _ (fun i => x i) at h
  rw [qmaQuadratic_sub] at h
  have hs : qmaQuadratic ((4:ℂ) • (1-qmaFourTensorProjection n)) (fun i => x i) =
      4*qmaQuadratic (1-qmaFourTensorProjection n) (fun i => x i) := by
    simpa only [Complex.ofReal_ofNat] using
      qmaQuadratic_smul (1-qmaFourTensorProjection n) (4:ℝ) (fun i => x i)
  rw [hs,qmaQuadratic_sub,hzero,hone] at h
  linarith

end ContinuumCoulomb

end

end OAI
