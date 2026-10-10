import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourProjector

namespace OAI

/-! Exact logical actions of the six physical exchanges in the singlet code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourLogical (i j : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) then !![-3,0;0,1]
  else if (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3) then !![0,-(Real.sqrt 3:ℂ);-(Real.sqrt 3:ℂ),-2]
  else !![0,(Real.sqrt 3:ℂ);(Real.sqrt 3:ℂ),-2]

theorem qmaFourLogical_normalize (i j : Fin 4) :
    (qmaFourRawLogical i j).map (Rat.castHom ℂ)*qmaFourNormalization =
      qmaFourNormalization*qmaFourLogical i j := by
  have hs0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsc : (Real.sqrt 3:ℂ) ≠ 0 := by exact_mod_cast hs0
  have hs : (Real.sqrt 3:ℂ)^2 = 3 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  unfold qmaFourRawLogical qmaFourLogical
  split_ifs <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourNormalization,Matrix.mul_apply,Matrix.diagonal_apply,Matrix.map_apply,Fin.sum_univ_two]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp [hs]

theorem qmaFourEncoding_action (i j : Fin 4) (hij : i < j) :
    qmaFourExchange i j*qmaFourEncoding = qmaFourEncoding*qmaFourLogical i j := by
  have he := congrArg (fun M : Matrix (Fin 16) (Fin 2) ℚ => M.map (Rat.castHom ℂ))
    (qmaFourRawEncoding_action i j hij)
  rw [Matrix.map_mul,Matrix.map_mul] at he
  change qmaFourExchange i j*qmaFourRawComplex =
    qmaFourRawComplex*(qmaFourRawLogical i j).map (Rat.castHom ℂ) at he
  rw [qmaFourEncoding,← Matrix.mul_assoc,he,Matrix.mul_assoc,qmaFourLogical_normalize,
    ← Matrix.mul_assoc]

theorem qmaFourEncoding_compression (i j : Fin 4) (hij : i < j) :
    qmaFourEncoding.conjTranspose*qmaFourExchange i j*qmaFourEncoding = qmaFourLogical i j := by
  rw [Matrix.mul_assoc,qmaFourEncoding_action i j hij,← Matrix.mul_assoc,qmaFourEncoding_gram,
    Matrix.one_mul]

theorem qmaFourLogical_Z : qmaFourLogical 0 1 = -(1 : Matrix (Fin 2) (Fin 2) ℂ)-(2:ℂ) • pauliZ := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [qmaFourLogical,pauliZ,Matrix.one_apply]

theorem qmaFourLogical_X : qmaFourLogical 0 3-qmaFourLogical 0 2 =
    (2*(Real.sqrt 3:ℂ)) • pauliX := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [qmaFourLogical,pauliX]
  all_goals ring

end ContinuumCoulomb

end

end OAI
