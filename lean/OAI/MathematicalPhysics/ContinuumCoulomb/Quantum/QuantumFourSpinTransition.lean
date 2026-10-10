import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourSpinCertificate

namespace OAI

/-! Single-spin transitions leave the singlet code and have penalty four. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourSpin_star (i : Fin 4) (μ : Fin 3) :
    (qmaFourSpin i μ).conjTranspose = qmaFourSpin i μ := by
  rw [qmaFourSpin_source,Matrix.conjTranspose_submatrix,sourceLocalPauli_star]

theorem qmaFourSpin_orthogonal (i : Fin 4) (μ : Fin 3) :
    qmaFourEncoding.conjTranspose*qmaFourSpin i μ*qmaFourEncoding = 0 := by
  rw [Matrix.mul_assoc,qmaFourSpin_encoding,Matrix.mul_smul]
  have he : qmaFourEncoding.conjTranspose*
      ((qmaFourSpinRawAction i μ).map (Rat.castHom ℂ)*qmaFourNormalization) = 0 := by
    rw [qmaFourEncoding,Matrix.conjTranspose_mul,qmaFourRawComplex_adjoint]
    calc
      _ = qmaFourNormalization.conjTranspose*
          ((qmaFourRawEncoding.transpose*qmaFourSpinRawAction i μ).map (Rat.castHom ℂ))*
          qmaFourNormalization := by rw [Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [qmaFourSpinRawAction_orthogonal]; simp
  rw [he,smul_zero]

theorem qmaFourSpin_excitation (i : Fin 4) (μ : Fin 3) :
    qmaFourPenalty*(qmaFourSpin i μ*qmaFourEncoding) =
      (4:ℂ) • (qmaFourSpin i μ*qmaFourEncoding) := by
  rw [qmaFourSpin_encoding,Matrix.mul_smul,← Matrix.mul_assoc,qmaFourPenalty,
    ← Matrix.map_mul,qmaFourSpinRawAction_eigen]
  have he : ((4:ℚ) • qmaFourSpinRawAction i μ).map (Rat.castHom ℂ) =
      (4:ℂ) • (qmaFourSpinRawAction i μ).map (Rat.castHom ℂ) := by
    ext s b
    simp
  rw [he,Matrix.smul_mul,smul_comm]

end ContinuumCoulomb

end

end OAI
