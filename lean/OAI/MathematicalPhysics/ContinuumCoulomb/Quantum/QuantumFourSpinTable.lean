import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourSpinCertificate

namespace OAI

/-! Sparse rational tables for the four-spin contractions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourSpinTable00 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,-1,1,0,0,0,0,0,0,0,0,0,0,1,-1,0] s
  else ![0,-1,-1,0,2,0,0,0,0,0,0,2,0,-1,-1,0] s

theorem qmaFourSpinRawAction_table00 :
    qmaFourSpinRawAction 0 0 = qmaFourSpinTable00 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinTable00,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def]

def qmaFourSpinTable01 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,1,-1,0,0,0,0,0,0,0,0,0,0,1,-1,0] s
  else ![0,1,1,0,-2,0,0,0,0,0,0,2,0,-1,-1,0] s

theorem qmaFourSpinRawAction_table01 :
    qmaFourSpinRawAction 0 1 = qmaFourSpinTable01 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinTable01,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def]

def qmaFourSpinTable02 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,0,0,0,0,1,-1,0,0,1,-1,0,0,0,0,0] s
  else ![0,0,0,2,0,-1,-1,0,0,1,1,0,-2,0,0,0] s

theorem qmaFourSpinRawAction_table02 :
    qmaFourSpinRawAction 0 2 = qmaFourSpinTable02 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinTable02,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def]

def qmaFourSpinTable10 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,1,-1,0,0,0,0,0,0,0,0,0,0,-1,1,0] s
  else ![0,-1,-1,0,0,0,0,2,2,0,0,0,0,-1,-1,0] s

theorem qmaFourSpinRawAction_table10 :
    qmaFourSpinRawAction 1 0 = qmaFourSpinTable10 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinTable10,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def]

def qmaFourSpinTable11 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,-1,1,0,0,0,0,0,0,0,0,0,0,-1,1,0] s
  else ![0,1,1,0,0,0,0,2,-2,0,0,0,0,-1,-1,0] s

theorem qmaFourSpinRawAction_table11 :
    qmaFourSpinRawAction 1 1 = qmaFourSpinTable11 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinTable11,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def]

def qmaFourSpinTable12 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,0,0,0,0,-1,1,0,0,-1,1,0,0,0,0,0] s
  else ![0,0,0,2,0,1,1,0,0,-1,-1,0,-2,0,0,0] s

theorem qmaFourSpinRawAction_table12 :
    qmaFourSpinRawAction 1 2 = qmaFourSpinTable12 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinTable12,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def]

def qmaFourSpinTable20 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,0,0,0,-1,0,0,1,1,0,0,-1,0,0,0,0] s
  else ![0,2,0,0,-1,0,0,-1,-1,0,0,-1,0,0,2,0] s

theorem qmaFourSpinRawAction_table20 :
    qmaFourSpinRawAction 2 0 = qmaFourSpinTable20 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinTable20,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def]

def qmaFourSpinTable21 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,0,0,0,1,0,0,1,-1,0,0,-1,0,0,0,0] s
  else ![0,-2,0,0,1,0,0,-1,1,0,0,-1,0,0,2,0] s

theorem qmaFourSpinRawAction_table21 :
    qmaFourSpinRawAction 2 1 = qmaFourSpinTable21 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinTable21,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def]

def qmaFourSpinTable22 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,0,0,0,0,1,1,0,0,-1,-1,0,0,0,0,0] s
  else ![0,0,0,-2,0,-1,1,0,0,-1,1,0,2,0,0,0] s

theorem qmaFourSpinRawAction_table22 :
    qmaFourSpinRawAction 2 2 = qmaFourSpinTable22 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinTable22,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def]

def qmaFourSpinTable30 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,0,0,0,1,0,0,-1,-1,0,0,1,0,0,0,0] s
  else ![0,0,2,0,-1,0,0,-1,-1,0,0,-1,0,2,0,0] s

theorem qmaFourSpinRawAction_table30 :
    qmaFourSpinRawAction 3 0 = qmaFourSpinTable30 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinTable30,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def]

def qmaFourSpinTable31 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,0,0,0,-1,0,0,-1,1,0,0,1,0,0,0,0] s
  else ![0,0,-2,0,1,0,0,-1,1,0,0,-1,0,2,0,0] s

theorem qmaFourSpinRawAction_table31 :
    qmaFourSpinRawAction 3 1 = qmaFourSpinTable31 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinTable31,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def]

def qmaFourSpinTable32 : Matrix (Fin 16) (Fin 2) ℚ := fun s b =>
  if b = 0 then ![0,0,0,0,0,-1,-1,0,0,1,1,0,0,0,0,0] s
  else ![0,0,0,-2,0,1,-1,0,0,1,-1,0,2,0,0,0] s

theorem qmaFourSpinRawAction_table32 :
    qmaFourSpinRawAction 3 2 = qmaFourSpinTable32 := by
  ext s b
  fin_cases s <;> fin_cases b <;>
    norm_num [qmaFourSpinTable32,qmaFourSpinRawAction,qmaPhysicalPauliSign,
      qmaFourSpinIndex,qmaPauliBit,qmaFourIndex,qmaFourBits,qmaFourRawEncoding,
      qmaFourRaw0,qmaFourRaw1,Function.update_apply,Equiv.swap_apply_def]

def qmaFourSpinTable (i : Fin 4) (μ : Fin 3) : Matrix (Fin 16) (Fin 2) ℚ :=
  ![![qmaFourSpinTable00,qmaFourSpinTable01,qmaFourSpinTable02],![qmaFourSpinTable10,qmaFourSpinTable11,qmaFourSpinTable12],![qmaFourSpinTable20,qmaFourSpinTable21,qmaFourSpinTable22],![qmaFourSpinTable30,qmaFourSpinTable31,qmaFourSpinTable32]] i μ

theorem qmaFourSpinRawAction_table (i : Fin 4) (μ : Fin 3) :
    qmaFourSpinRawAction i μ = qmaFourSpinTable i μ := by
  fin_cases i
  · fin_cases μ
    · exact qmaFourSpinRawAction_table00
    · exact qmaFourSpinRawAction_table01
    · exact qmaFourSpinRawAction_table02
  · fin_cases μ
    · exact qmaFourSpinRawAction_table10
    · exact qmaFourSpinRawAction_table11
    · exact qmaFourSpinRawAction_table12
  · fin_cases μ
    · exact qmaFourSpinRawAction_table20
    · exact qmaFourSpinRawAction_table21
    · exact qmaFourSpinRawAction_table22
  · fin_cases μ
    · exact qmaFourSpinRawAction_table30
    · exact qmaFourSpinRawAction_table31
    · exact qmaFourSpinRawAction_table32

end ContinuumCoulomb

end

end OAI
