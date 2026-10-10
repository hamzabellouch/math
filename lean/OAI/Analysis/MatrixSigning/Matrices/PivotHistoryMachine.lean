import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedPortRunSpec
import OAI.Analysis.MatrixSigning.Matrices.SavedPivotPacketMachine

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def state (saved parentDim parentTape childDim childTape : List Bool) : Fin 35 → List Bool :=
  fun j => if j = 32 then saved else if j = 26 then parentDim else if j = 31 then parentTape
    else if j = 30 then childDim else if j = 23 then childTape else []

def savedPorts : Fin 5 ↪ Fin 35 := ⟨![32, 26, 31, 33, 34], by decide⟩
def saveProgram : Program 35 := liftPorts KS.W08.SavedPivotPacket.program savedPorts

def savedFrame (dim tape : List Bool) : List Bool :=
  KS.W01.frame (KS.W08.SavedPivotPacket.payload dim tape)

theorem save_spec (saved pd pt cd ct : List Bool) :
    RunSpec saveProgram (state saved pd pt cd ct)
      (state (savedFrame pd pt ++ saved) [] [] cd ct)
      (24 * pd.length + 8 * pt.length + 22) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec
    KS.W08.SavedPivotPacket.program savedPorts
    (KS.W08.SavedPivotPacket.workspace saved pd pt)
    (KS.W08.SavedPivotPacket.workspace (savedFrame pd pt ++ saved) [] [])
    _ _ _ (KS.W08.SavedPivotPacket.full_spec saved pd pt)
  · intro i; fin_cases i <;> simp [state, savedPorts, KS.W08.SavedPivotPacket.workspace]
  · intro i; fin_cases i <;> simp [state, savedPorts, KS.W08.SavedPivotPacket.workspace]
  · intro j hj
    have h32 : j ≠ 32 := by simpa [savedPorts] using hj 0
    have h26 : j ≠ 26 := by simpa [savedPorts] using hj 1
    have h31 : j ≠ 31 := by simpa [savedPorts] using hj 2
    simp [state, h32, h26, h31]

def restoreProgram : Program 35 := liftPorts KS.W08.SavedPivotPacket.popProgram savedPorts

theorem restore_spec (saved pd pt witness : List Bool) :
    RunSpec restoreProgram (state (savedFrame pd pt ++ saved) [] [] [] witness)
      (state saved pd pt [] witness) (9 * pd.length + 3 * pt.length + 7) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec
    KS.W08.SavedPivotPacket.popProgram savedPorts
    (KS.W08.SavedPivotPacket.workspace (savedFrame pd pt ++ saved) [] [])
    (KS.W08.SavedPivotPacket.workspace saved pd pt)
    _ _ _ (KS.W08.SavedPivotPacket.pop_spec saved pd pt)
  · intro i; fin_cases i <;> simp [state, savedPorts, KS.W08.SavedPivotPacket.workspace]
  · intro i; fin_cases i <;> simp [state, savedPorts, KS.W08.SavedPivotPacket.workspace]
  · intro j hj
    have h32 : j ≠ 32 := by simpa [savedPorts] using hj 0
    have h26 : j ≠ 26 := by simpa [savedPorts] using hj 1
    have h31 : j ≠ 31 := by simpa [savedPorts] using hj 2
    simp [state, h32, h26, h31]

def descendProgram : Program 35 := compose
  (compose saveProgram (KS.W07.WireAppend.program 23 31 33))
  (KS.W07.WireAppend.program 30 26 33)

theorem descend_spec (saved pd pt cd ct : List Bool) :
    RunSpec descendProgram (state saved pd pt cd ct)
      (state (savedFrame pd pt ++ saved) cd ct [] [])
      (24 * pd.length + 8 * pt.length + 2 * cd.length + 2 * ct.length + 26) := by
  have h1 := save_spec saved pd pt cd ct
  have h2 := KS.W07.WireAppend.spec (23 : Fin 35) 31 33 (by decide) (by decide) (by decide)
    (state (savedFrame pd pt ++ saved) [] [] cd ct) rfl
  have e2 : KS.W07.WireAppend.after 23 31
      (state (savedFrame pd pt ++ saved) [] [] cd ct) =
      state (savedFrame pd pt ++ saved) [] ct cd [] := by
    funext j; fin_cases j <;> simp [state, KS.W07.WireAppend.after]
  rw [e2] at h2
  have h3 := KS.W07.WireAppend.spec (30 : Fin 35) 26 33 (by decide) (by decide) (by decide)
    (state (savedFrame pd pt ++ saved) [] ct cd []) rfl
  have e3 : KS.W07.WireAppend.after 30 26
      (state (savedFrame pd pt ++ saved) [] ct cd []) =
      state (savedFrame pd pt ++ saved) cd ct [] [] := by
    funext j; fin_cases j <;> simp [state, KS.W07.WireAppend.after]
  rw [e3] at h3
  have h := (h1.compose h2).compose h3
  convert h using 1 <;> simp [descendProgram, state]
  omega

end KS.W17.FixedPSD

end

end OAI
