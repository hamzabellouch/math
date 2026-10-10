import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourCorrelationCertificate
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourSpinTransition

namespace OAI

/-! Isotropic physical-spin correlations in the normalized singlet code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourCorrelation (i j : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if i = j then 1 else (1/3:ℂ) • qmaFourLogical (min i j) (max i j)

theorem qmaFourCorrelation_comm (i j : Fin 4) : qmaFourCorrelation i j = qmaFourCorrelation j i := by
  simp only [qmaFourCorrelation,eq_comm,min_comm,max_comm]

theorem qmaFourNormalization_gram :
    qmaFourNormalization.conjTranspose*
      (Matrix.diagonal ![(4:ℚ),12]).map (Rat.castHom ℂ)*qmaFourNormalization = 1 := by
  have he := qmaFourEncoding_gram
  rw [qmaFourEncoding,Matrix.conjTranspose_mul,qmaFourRawComplex_adjoint,
    qmaFourRawComplex] at he
  calc
    _ = qmaFourNormalization.conjTranspose*
        ((qmaFourRawEncoding.transpose*qmaFourRawEncoding).map (Rat.castHom ℂ))*
        qmaFourNormalization := by rw [qmaFourRawEncoding_gram]
    _ = 1 := by rw [Matrix.map_mul]; simpa only [Matrix.mul_assoc] using he

theorem qmaFourRawCorrelation_normalized (i j : Fin 4) :
    qmaFourNormalization.conjTranspose*(qmaFourRawCorrelation i j).map (Rat.castHom ℂ)*
      qmaFourNormalization = qmaFourCorrelation i j := by
  by_cases hij : i = j
  · simp only [qmaFourRawCorrelation,qmaFourCorrelation,hij,ite_true]
    exact qmaFourNormalization_gram
  · simp only [qmaFourRawCorrelation,qmaFourCorrelation,hij,ite_false]
    have hmap : ((1/3:ℚ) • (Matrix.diagonal ![(4:ℚ),12]*
        qmaFourRawLogical (min i j) (max i j))).map (Rat.castHom ℂ) =
        (1/3:ℂ) • ((Matrix.diagonal ![(4:ℚ),12]).map (Rat.castHom ℂ)*
          (qmaFourRawLogical (min i j) (max i j)).map (Rat.castHom ℂ)) := by
      calc
        _ = (1/3:ℂ) • ((Matrix.diagonal ![(4:ℚ),12]*
            qmaFourRawLogical (min i j) (max i j)).map (Rat.castHom ℂ)) := by
          ext a b
          simp
        _ = _ := by rw [Matrix.map_mul]
    rw [hmap,Matrix.mul_smul,Matrix.smul_mul]
    congr 1
    calc
      _ = qmaFourNormalization.conjTranspose*
          (Matrix.diagonal ![(4:ℚ),12]).map (Rat.castHom ℂ)*
          ((qmaFourRawLogical (min i j) (max i j)).map (Rat.castHom ℂ)*
            qmaFourNormalization) := by simp only [Matrix.mul_assoc]
      _ = qmaFourNormalization.conjTranspose*
          (Matrix.diagonal ![(4:ℚ),12]).map (Rat.castHom ℂ)*
          (qmaFourNormalization*qmaFourLogical (min i j) (max i j)) := by
        rw [qmaFourLogical_normalize]
      _ = _ := by rw [← Matrix.mul_assoc,qmaFourNormalization_gram,Matrix.one_mul]

theorem qmaFourPauliPhase_norm (μ : Fin 3) :
    star (qmaPauliPhase μ)*qmaPauliPhase μ = 1 := by
  fin_cases μ <;> norm_num [qmaPauliPhase,Complex.star_def]

theorem qmaFourSpin_correlation (i j : Fin 4) (μ ν : Fin 3) :
    (qmaFourSpin i μ*qmaFourEncoding).conjTranspose*(qmaFourSpin j ν*qmaFourEncoding) =
      if μ = ν then qmaFourCorrelation i j else 0 := by
  rw [qmaFourSpin_encoding,qmaFourSpin_encoding,Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul,qmaRatMatrix_adjoint,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have he : (qmaFourNormalization.conjTranspose*
      (qmaFourSpinRawAction i μ).transpose.map (Rat.castHom ℂ))*
      ((qmaFourSpinRawAction j ν).map (Rat.castHom ℂ)*qmaFourNormalization) =
      qmaFourNormalization.conjTranspose*
        ((qmaFourSpinRawAction i μ).transpose*qmaFourSpinRawAction j ν).map (Rat.castHom ℂ)*
        qmaFourNormalization := by
    rw [Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  rw [he,qmaFourRawCorrelation_eq]
  by_cases h : μ = ν
  · subst ν
    rw [ite_eq_left (rfl : μ = μ),qmaFourRawCorrelation_normalized,
      ite_eq_left (rfl : μ = μ),qmaFourPauliPhase_norm,one_smul]
  · simp [h]

end ContinuumCoulomb

end

end OAI
