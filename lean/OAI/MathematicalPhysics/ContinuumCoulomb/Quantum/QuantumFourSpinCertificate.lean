import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourSpin

namespace OAI

/-! Fixed rational certificates for the one-spin excited columns. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourPenaltyRational_mulVec (v : Fin 16 → ℚ) (s : Fin 16) :
    (qmaFourPenaltyRational *ᵥ v) s = 2*(
      v (qmaFourIndex (sourceSpinSwap 0 1 (qmaFourBits s)))+
      v (qmaFourIndex (sourceSpinSwap 0 2 (qmaFourBits s)))+
      v (qmaFourIndex (sourceSpinSwap 0 3 (qmaFourBits s)))+
      v (qmaFourIndex (sourceSpinSwap 1 2 (qmaFourBits s)))+
      v (qmaFourIndex (sourceSpinSwap 1 3 (qmaFourBits s)))+
      v (qmaFourIndex (sourceSpinSwap 2 3 (qmaFourBits s)))) := by
  simp only [qmaFourPenaltyRational,Matrix.add_mulVec,Pi.add_apply,Matrix.smul_mulVec,
    Matrix.one_mulVec,Pi.smul_apply,smul_eq_mul,qmaFourExchangeRational_mulVec]
  ring

theorem qmaFourSpinRawAction_orthogonal00 :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction 0 0 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
      qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def]

theorem qmaFourSpinRawAction_eigen00 :
    qmaFourPenaltyRational*qmaFourSpinRawAction 0 0 =
      (4:ℚ) • qmaFourSpinRawAction 0 0 := by
  ext s b
  change (qmaFourPenaltyRational *ᵥ fun t => qmaFourSpinRawAction 0 0 t b) s = _
  rw [qmaFourPenaltyRational_mulVec]
  simp only [Matrix.smul_apply,smul_eq_mul]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def,sourceSpinSwap_apply]

theorem qmaFourSpinRawAction_orthogonal01 :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction 0 1 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
      qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def]

theorem qmaFourSpinRawAction_eigen01 :
    qmaFourPenaltyRational*qmaFourSpinRawAction 0 1 =
      (4:ℚ) • qmaFourSpinRawAction 0 1 := by
  ext s b
  change (qmaFourPenaltyRational *ᵥ fun t => qmaFourSpinRawAction 0 1 t b) s = _
  rw [qmaFourPenaltyRational_mulVec]
  simp only [Matrix.smul_apply,smul_eq_mul]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def,sourceSpinSwap_apply]

theorem qmaFourSpinRawAction_orthogonal02 :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction 0 2 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
      qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def]

theorem qmaFourSpinRawAction_eigen02 :
    qmaFourPenaltyRational*qmaFourSpinRawAction 0 2 =
      (4:ℚ) • qmaFourSpinRawAction 0 2 := by
  ext s b
  change (qmaFourPenaltyRational *ᵥ fun t => qmaFourSpinRawAction 0 2 t b) s = _
  rw [qmaFourPenaltyRational_mulVec]
  simp only [Matrix.smul_apply,smul_eq_mul]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def,sourceSpinSwap_apply]

theorem qmaFourSpinRawAction_orthogonal10 :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction 1 0 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
      qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def]

theorem qmaFourSpinRawAction_eigen10 :
    qmaFourPenaltyRational*qmaFourSpinRawAction 1 0 =
      (4:ℚ) • qmaFourSpinRawAction 1 0 := by
  ext s b
  change (qmaFourPenaltyRational *ᵥ fun t => qmaFourSpinRawAction 1 0 t b) s = _
  rw [qmaFourPenaltyRational_mulVec]
  simp only [Matrix.smul_apply,smul_eq_mul]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def,sourceSpinSwap_apply]

theorem qmaFourSpinRawAction_orthogonal11 :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction 1 1 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
      qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def]

theorem qmaFourSpinRawAction_eigen11 :
    qmaFourPenaltyRational*qmaFourSpinRawAction 1 1 =
      (4:ℚ) • qmaFourSpinRawAction 1 1 := by
  ext s b
  change (qmaFourPenaltyRational *ᵥ fun t => qmaFourSpinRawAction 1 1 t b) s = _
  rw [qmaFourPenaltyRational_mulVec]
  simp only [Matrix.smul_apply,smul_eq_mul]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def,sourceSpinSwap_apply]

theorem qmaFourSpinRawAction_orthogonal12 :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction 1 2 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
      qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def]

theorem qmaFourSpinRawAction_eigen12 :
    qmaFourPenaltyRational*qmaFourSpinRawAction 1 2 =
      (4:ℚ) • qmaFourSpinRawAction 1 2 := by
  ext s b
  change (qmaFourPenaltyRational *ᵥ fun t => qmaFourSpinRawAction 1 2 t b) s = _
  rw [qmaFourPenaltyRational_mulVec]
  simp only [Matrix.smul_apply,smul_eq_mul]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def,sourceSpinSwap_apply]

theorem qmaFourSpinRawAction_orthogonal20 :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction 2 0 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
      qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def]

theorem qmaFourSpinRawAction_eigen20 :
    qmaFourPenaltyRational*qmaFourSpinRawAction 2 0 =
      (4:ℚ) • qmaFourSpinRawAction 2 0 := by
  ext s b
  change (qmaFourPenaltyRational *ᵥ fun t => qmaFourSpinRawAction 2 0 t b) s = _
  rw [qmaFourPenaltyRational_mulVec]
  simp only [Matrix.smul_apply,smul_eq_mul]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def,sourceSpinSwap_apply]

theorem qmaFourSpinRawAction_orthogonal21 :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction 2 1 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
      qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def]

theorem qmaFourSpinRawAction_eigen21 :
    qmaFourPenaltyRational*qmaFourSpinRawAction 2 1 =
      (4:ℚ) • qmaFourSpinRawAction 2 1 := by
  ext s b
  change (qmaFourPenaltyRational *ᵥ fun t => qmaFourSpinRawAction 2 1 t b) s = _
  rw [qmaFourPenaltyRational_mulVec]
  simp only [Matrix.smul_apply,smul_eq_mul]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def,sourceSpinSwap_apply]

theorem qmaFourSpinRawAction_orthogonal22 :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction 2 2 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
      qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def]

theorem qmaFourSpinRawAction_eigen22 :
    qmaFourPenaltyRational*qmaFourSpinRawAction 2 2 =
      (4:ℚ) • qmaFourSpinRawAction 2 2 := by
  ext s b
  change (qmaFourPenaltyRational *ᵥ fun t => qmaFourSpinRawAction 2 2 t b) s = _
  rw [qmaFourPenaltyRational_mulVec]
  simp only [Matrix.smul_apply,smul_eq_mul]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def,sourceSpinSwap_apply]

theorem qmaFourSpinRawAction_orthogonal30 :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction 3 0 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
      qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def]

theorem qmaFourSpinRawAction_eigen30 :
    qmaFourPenaltyRational*qmaFourSpinRawAction 3 0 =
      (4:ℚ) • qmaFourSpinRawAction 3 0 := by
  ext s b
  change (qmaFourPenaltyRational *ᵥ fun t => qmaFourSpinRawAction 3 0 t b) s = _
  rw [qmaFourPenaltyRational_mulVec]
  simp only [Matrix.smul_apply,smul_eq_mul]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def,sourceSpinSwap_apply]

theorem qmaFourSpinRawAction_orthogonal31 :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction 3 1 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
      qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def]

theorem qmaFourSpinRawAction_eigen31 :
    qmaFourPenaltyRational*qmaFourSpinRawAction 3 1 =
      (4:ℚ) • qmaFourSpinRawAction 3 1 := by
  ext s b
  change (qmaFourPenaltyRational *ᵥ fun t => qmaFourSpinRawAction 3 1 t b) s = _
  rw [qmaFourPenaltyRational_mulVec]
  simp only [Matrix.smul_apply,smul_eq_mul]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def,sourceSpinSwap_apply]

theorem qmaFourSpinRawAction_orthogonal32 :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction 3 2 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
      qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def]

theorem qmaFourSpinRawAction_eigen32 :
    qmaFourPenaltyRational*qmaFourSpinRawAction 3 2 =
      (4:ℚ) • qmaFourSpinRawAction 3 2 := by
  ext s b
  change (qmaFourPenaltyRational *ᵥ fun t => qmaFourSpinRawAction 3 2 t b) s = _
  rw [qmaFourPenaltyRational_mulVec]
  simp only [Matrix.smul_apply,smul_eq_mul]
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinRawAction,qmaPhysicalPauliSign,qmaFourSpinIndex,qmaPauliBit,
      qmaFourRawEncoding,qmaFourRaw0,qmaFourRaw1,qmaFourIndex,qmaFourBits,
      Function.update_apply,Equiv.swap_apply_def,sourceSpinSwap_apply]

theorem qmaFourSpinRawAction_orthogonal (i : Fin 4) (μ : Fin 3) :
    qmaFourRawEncoding.transpose*qmaFourSpinRawAction i μ = 0 := by
  fin_cases i
  · fin_cases μ
    · exact qmaFourSpinRawAction_orthogonal00
    · exact qmaFourSpinRawAction_orthogonal01
    · exact qmaFourSpinRawAction_orthogonal02
  · fin_cases μ
    · exact qmaFourSpinRawAction_orthogonal10
    · exact qmaFourSpinRawAction_orthogonal11
    · exact qmaFourSpinRawAction_orthogonal12
  · fin_cases μ
    · exact qmaFourSpinRawAction_orthogonal20
    · exact qmaFourSpinRawAction_orthogonal21
    · exact qmaFourSpinRawAction_orthogonal22
  · fin_cases μ
    · exact qmaFourSpinRawAction_orthogonal30
    · exact qmaFourSpinRawAction_orthogonal31
    · exact qmaFourSpinRawAction_orthogonal32

theorem qmaFourSpinRawAction_eigen (i : Fin 4) (μ : Fin 3) :
    qmaFourPenaltyRational*qmaFourSpinRawAction i μ = (4:ℚ) • qmaFourSpinRawAction i μ := by
  fin_cases i
  · fin_cases μ
    · exact qmaFourSpinRawAction_eigen00
    · exact qmaFourSpinRawAction_eigen01
    · exact qmaFourSpinRawAction_eigen02
  · fin_cases μ
    · exact qmaFourSpinRawAction_eigen10
    · exact qmaFourSpinRawAction_eigen11
    · exact qmaFourSpinRawAction_eigen12
  · fin_cases μ
    · exact qmaFourSpinRawAction_eigen20
    · exact qmaFourSpinRawAction_eigen21
    · exact qmaFourSpinRawAction_eigen22
  · fin_cases μ
    · exact qmaFourSpinRawAction_eigen30
    · exact qmaFourSpinRawAction_eigen31
    · exact qmaFourSpinRawAction_eigen32

end ContinuumCoulomb

end

end OAI
