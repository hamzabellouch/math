import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.FrameWireCodec
import OAI.Analysis.MatrixSigning.Encoding.WireAppend

namespace OAI

section

namespace KS.W08.SavedPivotPacket
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.FixedPositiveSerializer (registers)

theorem frame_at {k : ℕ} (ports : Fin 3 ↪ Fin k) (before : Fin k → List Bool)
    (payload : List Bool) (h0 : before (ports 0) = []) (h1 : before (ports 1) = payload)
    (h2 : before (ports 2) = []) :
    RunSpec (KS.W11.FrameWireCodec.frameProgram ports) before
      (Function.update before (ports 1) (KS.W01.frame payload)) (4 * payload.length + 3) := by
  have h := KS.W11.FrameWireCodec.frame_spec ports before payload
  have hi : registers ports before [] payload [] = before := by
    funext j
    by_cases hj0 : j = ports 0
    · subst j; simp [registers, h0]
    · by_cases hj1 : j = ports 1
      · subst j; simp [registers, hj0, h1]
      · by_cases hj2 : j = ports 2
        · subst j; simp [registers, hj0, hj1, h2]
        · simp [registers, hj0, hj1, hj2]
  have ho : registers ports before [] (KS.W01.frame payload) [] =
      Function.update before (ports 1) (KS.W01.frame payload) := by
    funext j
    by_cases hj0 : j = ports 0
    · subst j; simp [registers, Function.update, h0, ports.injective.eq_iff]
    · by_cases hj1 : j = ports 1
      · subst j; simp [registers, hj0, Function.update]
      · by_cases hj2 : j = ports 2
        · subst j; simp [registers, hj0, hj1, h2, Function.update]
        · simp [registers, hj0, hj1, hj2, Function.update]
  rw [hi, ho] at h
  exact h

def workspace (saved dim row : List Bool) : Fin 5 → List Bool := ![saved, dim, row, [], []]
def dimPorts : Fin 3 ↪ Fin 5 := ⟨![3, 1, 4], by decide⟩
def packetPorts : Fin 3 ↪ Fin 5 := ⟨![1, 2, 4], by decide⟩
def payload (dim row : List Bool) : List Bool := KS.W01.frame dim ++ row

def program : Program 5 := compose
  (compose (compose (KS.W11.FrameWireCodec.frameProgram dimPorts)
    (KS.W07.WireAppend.program 1 2 3))
    (KS.W11.FrameWireCodec.frameProgram packetPorts))
  (KS.W07.WireAppend.program 2 0 3)

theorem full_spec (saved dim row : List Bool) :
    RunSpec program (workspace saved dim row)
      (workspace (KS.W01.frame (payload dim row) ++ saved) [] [])
      (24 * dim.length + 8 * row.length + 22) := by
  have h1 := frame_at dimPorts (workspace saved dim row) dim rfl rfl rfl
  have e1 : Function.update (workspace saved dim row) (dimPorts 1) (KS.W01.frame dim) =
      workspace saved (KS.W01.frame dim) row := by
    funext j; fin_cases j <;> simp [workspace, dimPorts, Function.update]
  rw [e1] at h1
  have h2 := KS.W07.WireAppend.spec (1 : Fin 5) 2 3 (by decide) (by decide) (by decide)
    (workspace saved (KS.W01.frame dim) row) rfl
  have e2 : KS.W07.WireAppend.after 1 2 (workspace saved (KS.W01.frame dim) row) =
      workspace saved [] (payload dim row) := by
    funext j; fin_cases j <;> simp [workspace, payload, KS.W07.WireAppend.after]
  rw [e2] at h2
  have h3 := frame_at packetPorts (workspace saved [] (payload dim row)) (payload dim row) rfl rfl rfl
  have e3 : Function.update (workspace saved [] (payload dim row)) (packetPorts 1)
      (KS.W01.frame (payload dim row)) = workspace saved [] (KS.W01.frame (payload dim row)) := by
    funext j; fin_cases j <;> simp [workspace, packetPorts, Function.update]
  rw [e3] at h3
  have h4 := KS.W07.WireAppend.spec (2 : Fin 5) 0 3 (by decide) (by decide) (by decide)
    (workspace saved [] (KS.W01.frame (payload dim row))) rfl
  have e4 : KS.W07.WireAppend.after 2 0 (workspace saved [] (KS.W01.frame (payload dim row))) =
      workspace (KS.W01.frame (payload dim row) ++ saved) [] [] := by
    funext j; fin_cases j <;> simp [workspace, KS.W07.WireAppend.after]
  rw [e4] at h4
  have h := ((h1.compose h2).compose h3).compose h4
  have ht : (((4 * dim.length + 3) +
      (2 * (workspace saved (KS.W01.frame dim) row 1).length + 2)) +
      (4 * (payload dim row).length + 3)) +
      (2 * (workspace saved [] (KS.W01.frame (payload dim row)) 2).length + 2) =
      24 * dim.length + 8 * row.length + 22 := by
    change (((4 * dim.length + 3) + (2 * (KS.W01.frame dim).length + 2)) +
      (4 * (payload dim row).length + 3)) +
      (2 * (KS.W01.frame (payload dim row)).length + 2) = _
    simp only [payload, List.length_append, KS.W01.length_frame]
    omega
  rw [ht] at h
  exact h

def outerPorts : Fin 3 ↪ Fin 5 := ⟨![0, 2, 3], by decide⟩
def innerPorts : Fin 3 ↪ Fin 5 := ⟨![2, 1, 3], by decide⟩
def popProgram : Program 5 := compose
  (KS.W11.FrameWireCodec.unframeProgram outerPorts)
  (KS.W11.FrameWireCodec.unframeProgram innerPorts)

theorem pop_spec (saved dim row : List Bool) :
    RunSpec popProgram (workspace (KS.W01.frame (payload dim row) ++ saved) [] [])
      (workspace saved dim row) (9 * dim.length + 3 * row.length + 7) := by
  have h1 := KS.W11.FrameWireCodec.unframe_spec outerPorts (workspace [] [] [])
    (payload dim row) saved
  have e1 : registers outerPorts (workspace [] [] [])
      (KS.W01.frame (payload dim row) ++ saved) [] [] =
      workspace (KS.W01.frame (payload dim row) ++ saved) [] [] := by
    funext j; fin_cases j <;> simp [registers, outerPorts, workspace]
  have e2 : registers outerPorts (workspace [] [] []) saved (payload dim row) [] =
      workspace saved [] (payload dim row) := by
    funext j; fin_cases j <;> simp [registers, outerPorts, workspace]
  rw [e1, e2] at h1
  have h2 := KS.W11.FrameWireCodec.unframe_spec innerPorts (workspace saved [] []) dim row
  have e3 : registers innerPorts (workspace saved [] []) (KS.W01.frame dim ++ row) [] [] =
      workspace saved [] (payload dim row) := by
    funext j; fin_cases j <;> simp [registers, innerPorts, workspace, payload]
  have e4 : registers innerPorts (workspace saved [] []) row dim [] = workspace saved dim row := by
    funext j; fin_cases j <;> simp [registers, innerPorts, workspace]
  rw [e3, e4] at h2
  have h := h1.compose h2
  have ht : (3 * (payload dim row).length + 2) + (3 * dim.length + 2) =
      9 * dim.length + 3 * row.length + 7 := by
    simp only [payload, List.length_append, KS.W01.length_frame]
    omega
  rw [ht] at h
  exact h

end KS.W08.SavedPivotPacket

end

end OAI
