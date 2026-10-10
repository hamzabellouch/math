import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourEncoding

namespace OAI

/-! Normalization of the two exact singlet columns. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourRawComplex : Matrix (Fin 16) (Fin 2) ℂ :=
  qmaFourRawEncoding.map (Rat.castHom ℂ)

def qmaFourNormalization : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![1/2,1/(2*(Real.sqrt 3:ℝ))]

def qmaFourEncoding : Matrix (Fin 16) (Fin 2) ℂ := qmaFourRawComplex*qmaFourNormalization

theorem qmaFourRawComplex_adjoint : qmaFourRawComplex.conjTranspose =
    qmaFourRawEncoding.transpose.map (Rat.castHom ℂ) := by
  ext b s
  simp [qmaFourRawComplex,Matrix.conjTranspose_apply,Matrix.transpose_apply]

theorem qmaFourRawComplex_gram : qmaFourRawComplex.conjTranspose*qmaFourRawComplex =
    Matrix.diagonal ![(4:ℂ),12] := by
  rw [qmaFourRawComplex_adjoint]
  change qmaFourRawEncoding.transpose.map (Rat.castHom ℂ)*
    qmaFourRawEncoding.map (Rat.castHom ℂ) = _
  rw [← Matrix.map_mul,qmaFourRawEncoding_gram]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [Matrix.diagonal_apply]

theorem qmaFourEncoding_gram : qmaFourEncoding.conjTranspose*qmaFourEncoding = 1 := by
  have hs0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsc : (Real.sqrt 3:ℂ) ≠ 0 := by exact_mod_cast hs0
  have hs : (Real.sqrt 3:ℂ)^2 = 3 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have htwo : (starRingEnd ℂ) (2:ℂ) = 2 := by
    exact Complex.conj_ofReal 2
  calc
    _ = qmaFourNormalization.conjTranspose*(qmaFourRawComplex.conjTranspose*qmaFourRawComplex)*
        qmaFourNormalization := by
      simp only [qmaFourEncoding,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = qmaFourNormalization.conjTranspose*Matrix.diagonal ![(4:ℂ),12]*qmaFourNormalization := by
      rw [qmaFourRawComplex_gram]
    _ = 1 := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        norm_num [qmaFourNormalization,Matrix.mul_apply,Matrix.conjTranspose_apply,
          Matrix.diagonal_apply,Matrix.one_apply,Fin.sum_univ_two,Complex.star_def,htwo]
      field_simp
      rw [hs]
      norm_num

end ContinuumCoulomb

end

end OAI
