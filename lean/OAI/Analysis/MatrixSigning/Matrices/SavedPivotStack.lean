import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.FrameWireCodec
import OAI.Analysis.MatrixSigning.Encoding.WireAppend

namespace OAI

section

namespace KS.W08.SavedPivotStack

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.FixedPositiveSerializer (registers)

def workspace (saved payload : List Bool) : Fin 4 → List Bool := ![saved, payload, [], []]

def framePorts : Fin 3 ↪ Fin 4 := ⟨![2, 1, 3], by decide⟩
def popPorts : Fin 3 ↪ Fin 4 := ⟨![0, 1, 2], by decide⟩

def pushProgram : Program 4 := compose
  (KS.W11.FrameWireCodec.frameProgram framePorts)
  (KS.W07.WireAppend.program 1 0 2)

def popProgram : Program 4 := KS.W11.FrameWireCodec.unframeProgram popPorts

theorem push_spec (saved payload : List Bool) :
    RunSpec pushProgram (workspace saved payload)
      (workspace (KS.W01.frame payload ++ saved) []) (8 * payload.length + 7) := by
  have hf := KS.W11.FrameWireCodec.frame_spec framePorts (workspace saved []) payload
  have hi : registers framePorts (workspace saved []) [] payload [] =
      workspace saved payload := by
    funext j
    fin_cases j <;> simp [registers, framePorts, workspace]
  have ho : registers framePorts (workspace saved []) [] (KS.W01.frame payload) [] =
      workspace saved (KS.W01.frame payload) := by
    funext j
    fin_cases j <;> simp [registers, framePorts, workspace]
  rw [hi, ho] at hf
  have ha := KS.W07.WireAppend.spec (1 : Fin 4) 0 2 (by decide) (by decide)
    (by decide) (workspace saved (KS.W01.frame payload)) rfl
  have he : KS.W07.WireAppend.after 1 0 (workspace saved (KS.W01.frame payload)) =
      workspace (KS.W01.frame payload ++ saved) [] := by
    funext j
    fin_cases j <;> simp [KS.W07.WireAppend.after, workspace]
  rw [he] at ha
  have h := hf.compose ha
  have ht : (4 * payload.length + 3) +
      (2 * (workspace saved (KS.W01.frame payload) 1).length + 2) =
      8 * payload.length + 7 := by
    change (4 * payload.length + 3) + (2 * (KS.W01.frame payload).length + 2) = _
    rw [KS.W01.length_frame]
    omega
  rw [ht] at h
  exact h

theorem pop_spec (saved payload : List Bool) :
    RunSpec popProgram (workspace (KS.W01.frame payload ++ saved) [])
      (workspace saved payload) (3 * payload.length + 2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec popPorts (workspace [] []) payload saved
  have hi : registers popPorts (workspace [] []) (KS.W01.frame payload ++ saved) [] [] =
      workspace (KS.W01.frame payload ++ saved) [] := by
    funext j
    fin_cases j <;> simp [registers, popPorts, workspace]
  have ho : registers popPorts (workspace [] []) saved payload [] =
      workspace saved payload := by
    funext j
    fin_cases j <;> simp [registers, popPorts, workspace]
  rw [hi, ho] at h
  exact h

def stackTape (payloads : List (List Bool)) : List Bool := payloads.flatMap KS.W01.frame

@[simp] theorem stackTape_cons (payload : List Bool) (tail : List (List Bool)) :
    stackTape (payload :: tail) = KS.W01.frame payload ++ stackTape tail := rfl

@[simp] theorem stackTape_nil : stackTape [] = [] := rfl

theorem push_stack_spec (tail : List (List Bool)) (payload : List Bool) :
    RunSpec pushProgram (workspace (stackTape tail) payload)
      (workspace (stackTape (payload :: tail)) []) (8 * payload.length + 7) :=
  push_spec _ _

theorem pop_stack_spec (tail : List (List Bool)) (payload : List Bool) :
    RunSpec popProgram (workspace (stackTape (payload :: tail)) [])
      (workspace (stackTape tail) payload) (3 * payload.length + 2) := pop_spec _ _

theorem stackTape_length (payloads : List (List Bool)) :
    (stackTape payloads).length = 2 * (payloads.map List.length).sum + payloads.length := by
  induction payloads with
  | nil => rfl
  | cons p ps ih => simp [stackTape_cons, KS.W01.length_frame, ih]; omega

theorem stackTape_length_le (payloads : List (List Bool)) (b : ℕ)
    (h : ∀ p ∈ payloads, p.length ≤ b) :
    (stackTape payloads).length ≤ payloads.length * (2 * b + 1) := by
  induction payloads with
  | nil => simp
  | cons p ps ih =>
    have hp := h p (by simp)
    have ht := ih (fun q hq => h q (by simp [hq]))
    simp only [stackTape_cons, List.length_append, KS.W01.length_frame, List.length_cons]
    calc
      2 * p.length + 1 + (stackTape ps).length ≤
          (2 * b + 1) + ps.length * (2 * b + 1) := by omega
      _ = (ps.length + 1) * (2 * b + 1) := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega

end KS.W08.SavedPivotStack

end

end OAI
