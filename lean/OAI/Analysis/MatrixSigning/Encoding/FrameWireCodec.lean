import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.FixedPositiveSerializer

namespace OAI

namespace KS.W11.FrameWireCodec
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.FixedPositiveSerializer (registers registers_port registers_other)

def inputAt {k : ℕ} (P : Program k) (port : Fin k) : Program k := { P with input := port }

theorem inputAt_step {k : ℕ} (P : Program k) (port : Fin k)
    (c : Config k P.states) (coin : Bool) :
    (inputAt P port).toMachine.step c coin = P.toMachine.step c coin := by
  cases c with
  | mk state «stacks» => cases state <;> rfl

theorem inputAt_run {k : ℕ} (P : Program k) (port : Fin k)
    (c : Config k P.states) (bits : List Bool) :
    (inputAt P port).toMachine.run c bits = P.toMachine.run c bits := by
  induction bits generalizing c with
  | nil => rfl
  | cons coin bits ih => erw [Machine.run.eq_2, inputAt_step, ih, Machine.run.eq_2]

def frameEmitter : KS.W29.BinaryMachine :=
  KS.W28.PositiveWireSerializer.machine.withEntry (2 : Fin 5)

def emitProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  inputAt (ofMachine (lift3 frameEmitter ports)) (ports 1)

def frameProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  compose (emitProgram ports) (KS.W28.FixedPositiveSerializer.reverseProgram ports)

theorem frameProgram_states {k : ℕ} (ports : Fin 3 ↪ Fin k) :
    (frameProgram ports).states = 8 := rfl

theorem frameProgram_input {k : ℕ} (ports : Fin 3 ↪ Fin k) :
    (frameProgram ports).input = ports 1 := rfl

theorem frameProgram_output {k : ℕ} (ports : Fin 3 ↪ Fin k) :
    (frameProgram ports).output = ports 1 := rfl

theorem emit_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (payload : List Bool) :
    RunSpec (emitProgram ports) (registers ports spare [] payload [])
      (registers ports spare [] [] (KS.W01.frame payload).reverse)
      (2 * payload.length + 1) := by
  intro bits hbits
  unfold emitProgram
  erw [inputAt_run]
  change (lift3 frameEmitter ports).run
    ⟨some (2 : Fin 5), registers ports spare [] payload []⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some (2 : Fin 5), registers ports spare [] payload []⟩ : Config k 5) =
        KS.W28.PositiveWireSerializer.cfg (some 2) [] payload [] := by
      change KS.W29.Config.mk (some (2 : Fin 5)) _ = KS.W29.Config.mk (some (2 : Fin 5)) _
      congr 1
      funext j
      simp
    erw [hp]
    unfold frameEmitter
    erw [KS.W29.BinaryMachine.withEntry_run,
      KS.W28.PositiveWireSerializer.run_den payload [] bits hbits]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    simp
  · intro j hj
    change registers ports spare _ _ _ j = registers ports spare _ _ _ j
    rw [registers_other _ _ _ _ _ _ hj, registers_other _ _ _ _ _ _ hj]

theorem frame_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (payload : List Bool) :
    RunSpec (frameProgram ports) (registers ports spare [] payload [])
      (registers ports spare [] (KS.W01.frame payload) []) (4 * payload.length + 3) := by
  have h := (emit_spec ports spare payload).compose
    (KS.W28.FixedPositiveSerializer.reverse_spec ports spare (KS.W01.frame payload))
  have ht : (2 * payload.length + 1) + ((KS.W01.frame payload).length + 1) =
      4 * payload.length + 3 := by rw [KS.W01.length_frame]; omega
  rw [ht] at h
  exact h

def unframeProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 KS.W29.FrameDecoder.machine ports)

theorem unframe_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (payload tail : List Bool) :
    RunSpec (unframeProgram ports) (registers ports spare (KS.W01.frame payload ++ tail) [] [])
      (registers ports spare tail payload []) (3 * payload.length + 2) := by
  intro bits hbits
  change (lift3 KS.W29.FrameDecoder.machine ports).run
    ⟨some (0 : Fin 3), registers ports spare (KS.W01.frame payload ++ tail) [] []⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports
        (⟨some (0 : Fin 3), registers ports spare (KS.W01.frame payload ++ tail) [] []⟩ : Config k 3) =
        KS.W29.FrameDecoder.machine.init (KS.W01.frame payload ++ tail) := by
      change KS.W29.Config.mk (some (0 : Fin 3)) _ = KS.W29.Config.mk (some (0 : Fin 3)) _
      congr 1
      funext j
      fin_cases j <;> simp [registers]
    erw [hp, KS.W29.FrameDecoder.run_frame payload tail bits hbits]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    simp
  · intro j hj
    change registers ports spare _ _ _ j = registers ports spare _ _ _ j
    rw [registers_other _ _ _ _ _ _ hj, registers_other _ _ _ _ _ _ hj]

theorem frame_rat_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (q : ℚ) :
    RunSpec (frameProgram ports) (registers ports spare [] (KS.W01.encodeRat q) [])
      (registers ports spare [] (KS.W01.frame (KS.W01.encodeRat q)) [])
      (4 * (KS.W01.encodeRat q).length + 3) := frame_spec ports spare _

end KS.W11.FrameWireCodec

end OAI
