import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourEncoding

namespace OAI

/-! A rational positive factorization of the four-spin penalty above the
singlet projection. Each fixed row is checked separately at default limits. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourProjectionRational : Matrix (Fin 16) (Fin 16) ℚ := fun s t =>
  qmaFourRaw0 s*qmaFourRaw0 t/4+qmaFourRaw1 s*qmaFourRaw1 t/12

def qmaFourPenaltyRational : Matrix (Fin 16) (Fin 16) ℚ :=
  qmaFourExchangeRational 0 1+qmaFourExchangeRational 0 2+qmaFourExchangeRational 0 3+
    qmaFourExchangeRational 1 2+qmaFourExchangeRational 1 3+qmaFourExchangeRational 2 3+(6:ℚ) • (1 : Matrix (Fin 16) (Fin 16) ℚ)

def qmaFourWeight (s : Fin 16) : Fin 5 :=
  ⟨s.val/8+s.val/4%2+s.val/2%2+s.val%2,by have hs := s.isLt; omega⟩

def qmaFourSymmetricWeights : Fin 5 → ℚ := ![8,2,4/3,2,8]

def qmaFourSymmetricRational : Matrix (Fin 16) (Fin 16) ℚ := fun s t =>
  if qmaFourWeight s = qmaFourWeight t then qmaFourSymmetricWeights (qmaFourWeight s) else 0

def qmaFourGapRational : Matrix (Fin 16) (Fin 16) ℚ :=
  qmaFourPenaltyRational-(4:ℚ) • (1-qmaFourProjectionRational)

theorem qmaFourGapRational_row0 (t : Fin 16) :
    qmaFourGapRational 0 t = qmaFourSymmetricRational 0 t := by
  fin_cases t <;>
    norm_num [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]

theorem qmaFourGapRational_row1 (t : Fin 16) :
    qmaFourGapRational 1 t = qmaFourSymmetricRational 1 t := by
  fin_cases t <;>
    norm_num [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]

theorem qmaFourGapRational_row2 (t : Fin 16) :
    qmaFourGapRational 2 t = qmaFourSymmetricRational 2 t := by
  fin_cases t <;>
    norm_num [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]

theorem qmaFourGapRational_row3 (t : Fin 16) :
    qmaFourGapRational 3 t = qmaFourSymmetricRational 3 t := by
  fin_cases t <;>
    norm_num [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]

theorem qmaFourGapRational_row4 (t : Fin 16) :
    qmaFourGapRational 4 t = qmaFourSymmetricRational 4 t := by
  fin_cases t <;>
    norm_num [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]

theorem qmaFourGapRational_row5 (t : Fin 16) :
    qmaFourGapRational 5 t = qmaFourSymmetricRational 5 t := by
  fin_cases t <;>
    norm_num [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]

theorem qmaFourGapRational_row6 (t : Fin 16) :
    qmaFourGapRational 6 t = qmaFourSymmetricRational 6 t := by
  fin_cases t <;>
    norm_num [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]

theorem qmaFourGapRational_row7 (t : Fin 16) :
    qmaFourGapRational 7 t = qmaFourSymmetricRational 7 t := by
  fin_cases t <;>
    norm_num [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]

theorem qmaFourGapRational_row8 (t : Fin 16) :
    qmaFourGapRational 8 t = qmaFourSymmetricRational 8 t := by
  fin_cases t <;>
    norm_num [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]

theorem qmaFourGapRational_row9 (t : Fin 16) :
    qmaFourGapRational 9 t = qmaFourSymmetricRational 9 t := by
  fin_cases t <;>
    norm_num [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]

theorem qmaFourGapRational_row10 (t : Fin 16) :
    qmaFourGapRational 10 t = qmaFourSymmetricRational 10 t := by
  fin_cases t <;>
    norm_num [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]

theorem qmaFourGapRational_row11 (t : Fin 16) :
    qmaFourGapRational 11 t = qmaFourSymmetricRational 11 t := by
  fin_cases t <;>
    norm_num [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]

theorem qmaFourGapRational_row12 (t : Fin 16) :
    qmaFourGapRational 12 t = qmaFourSymmetricRational 12 t := by
  fin_cases t <;>
    norm_num [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]

theorem qmaFourGapRational_row13 (t : Fin 16) :
    qmaFourGapRational 13 t = qmaFourSymmetricRational 13 t := by
  fin_cases t <;>
    norm_num [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]

theorem qmaFourGapRational_row14 (t : Fin 16) :
    qmaFourGapRational 14 t = qmaFourSymmetricRational 14 t := by
  fin_cases t <;>
    norm_num [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]

theorem qmaFourGapRational_row15 (t : Fin 16) :
    qmaFourGapRational 15 t = qmaFourSymmetricRational 15 t := by
  fin_cases t <;>
    norm_num [qmaFourGapRational,qmaFourPenaltyRational,qmaFourProjectionRational,
      qmaFourExchangeRational,qmaFourRaw0,qmaFourRaw1,qmaFourSymmetricRational,
      qmaFourSymmetricWeights,qmaFourWeight,qmaFourIndex,qmaFourBits,
      sourceSpinSwap_apply,Equiv.swap_apply_def,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]

theorem qmaFourGapRational_factor : qmaFourGapRational = qmaFourSymmetricRational := by
  ext s t
  fin_cases s
  · exact qmaFourGapRational_row0 t
  · exact qmaFourGapRational_row1 t
  · exact qmaFourGapRational_row2 t
  · exact qmaFourGapRational_row3 t
  · exact qmaFourGapRational_row4 t
  · exact qmaFourGapRational_row5 t
  · exact qmaFourGapRational_row6 t
  · exact qmaFourGapRational_row7 t
  · exact qmaFourGapRational_row8 t
  · exact qmaFourGapRational_row9 t
  · exact qmaFourGapRational_row10 t
  · exact qmaFourGapRational_row11 t
  · exact qmaFourGapRational_row12 t
  · exact qmaFourGapRational_row13 t
  · exact qmaFourGapRational_row14 t
  · exact qmaFourGapRational_row15 t

end ContinuumCoulomb

end

end OAI
