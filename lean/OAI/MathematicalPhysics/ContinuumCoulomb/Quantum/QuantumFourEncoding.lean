import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourBasis

namespace OAI

/-! The two rational singlet columns spanning the four-spin encoded qubit. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourRaw0 : Fin 16 → ℚ := ![0,0,0,0,0,1,-1,0,0,-1,1,0,0,0,0,0]
def qmaFourRaw1 : Fin 16 → ℚ := ![0,0,0,2,0,-1,-1,0,0,-1,-1,0,2,0,0,0]

def qmaFourRawEncoding : Matrix (Fin 16) (Fin 2) ℚ :=
  fun s b => if b = 0 then qmaFourRaw0 s else qmaFourRaw1 s

theorem qmaFourRawEncoding_gram : qmaFourRawEncoding.transpose*qmaFourRawEncoding =
    Matrix.diagonal ![(4:ℚ),12] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,Matrix.mul_apply,
      Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ]

theorem qmaFourExchangeRational_mulVec (i j : Fin 4) (v : Fin 16 → ℚ) (s : Fin 16) :
    (qmaFourExchangeRational i j *ᵥ v) s =
      2*v (qmaFourIndex (sourceSpinSwap i j (qmaFourBits s)))-v s := by
  simp only [qmaFourExchangeRational,Matrix.mulVec,dotProduct,sub_mul,
    Finset.sum_sub_distrib,mul_assoc,ite_mul,one_mul,zero_mul,← Finset.mul_sum]
  simp

def qmaFourRawLogical (i j : Fin 4) : Matrix (Fin 2) (Fin 2) ℚ :=
  if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) then !![-3,0;0,1]
  else if (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3) then !![0,-3;-1,-2]
  else !![0,3;1,-2]

theorem qmaFourRawEncoding_action01 :
    qmaFourExchangeRational 0 1*qmaFourRawEncoding = qmaFourRawEncoding*qmaFourRawLogical 0 1 := by
  ext s b
  change (qmaFourExchangeRational 0 1 *ᵥ fun t => qmaFourRawEncoding t b) s = _
  rw [qmaFourExchangeRational_mulVec]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourRawLogical,
      qmaFourIndex,qmaFourBits,sourceSpinSwap_apply,Equiv.swap_apply_def,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem qmaFourRawEncoding_action02 :
    qmaFourExchangeRational 0 2*qmaFourRawEncoding = qmaFourRawEncoding*qmaFourRawLogical 0 2 := by
  ext s b
  change (qmaFourExchangeRational 0 2 *ᵥ fun t => qmaFourRawEncoding t b) s = _
  rw [qmaFourExchangeRational_mulVec]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourRawLogical,
      qmaFourIndex,qmaFourBits,sourceSpinSwap_apply,Equiv.swap_apply_def,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem qmaFourRawEncoding_action03 :
    qmaFourExchangeRational 0 3*qmaFourRawEncoding = qmaFourRawEncoding*qmaFourRawLogical 0 3 := by
  ext s b
  change (qmaFourExchangeRational 0 3 *ᵥ fun t => qmaFourRawEncoding t b) s = _
  rw [qmaFourExchangeRational_mulVec]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourRawLogical,
      qmaFourIndex,qmaFourBits,sourceSpinSwap_apply,Equiv.swap_apply_def,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem qmaFourRawEncoding_action12 :
    qmaFourExchangeRational 1 2*qmaFourRawEncoding = qmaFourRawEncoding*qmaFourRawLogical 1 2 := by
  ext s b
  change (qmaFourExchangeRational 1 2 *ᵥ fun t => qmaFourRawEncoding t b) s = _
  rw [qmaFourExchangeRational_mulVec]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourRawLogical,
      qmaFourIndex,qmaFourBits,sourceSpinSwap_apply,Equiv.swap_apply_def,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem qmaFourRawEncoding_action13 :
    qmaFourExchangeRational 1 3*qmaFourRawEncoding = qmaFourRawEncoding*qmaFourRawLogical 1 3 := by
  ext s b
  change (qmaFourExchangeRational 1 3 *ᵥ fun t => qmaFourRawEncoding t b) s = _
  rw [qmaFourExchangeRational_mulVec]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourRawLogical,
      qmaFourIndex,qmaFourBits,sourceSpinSwap_apply,Equiv.swap_apply_def,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem qmaFourRawEncoding_action23 :
    qmaFourExchangeRational 2 3*qmaFourRawEncoding = qmaFourRawEncoding*qmaFourRawLogical 2 3 := by
  ext s b
  change (qmaFourExchangeRational 2 3 *ᵥ fun t => qmaFourRawEncoding t b) s = _
  rw [qmaFourExchangeRational_mulVec]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourRawLogical,
      qmaFourIndex,qmaFourBits,sourceSpinSwap_apply,Equiv.swap_apply_def,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem qmaFourRawEncoding_action (i j : Fin 4) (hij : i < j) :
    qmaFourExchangeRational i j*qmaFourRawEncoding = qmaFourRawEncoding*qmaFourRawLogical i j := by
  fin_cases i
  · fin_cases j
    · norm_num at hij
    · exact qmaFourRawEncoding_action01
    · exact qmaFourRawEncoding_action02
    · exact qmaFourRawEncoding_action03
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · exact qmaFourRawEncoding_action12
    · exact qmaFourRawEncoding_action13
  · fin_cases j
    · norm_num at hij
    · norm_num at hij
    · norm_num at hij
    · exact qmaFourRawEncoding_action23
  · fin_cases j <;> norm_num at hij

end ContinuumCoulomb

end

end OAI
