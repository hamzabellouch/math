import Mathlib
import OAI.Analysis.MatrixSigning.Machines.MachineTransport
import OAI.Analysis.MatrixSigning.Matrices.MatrixReadProgram
import OAI.Analysis.MatrixSigning.Matrices.RowDotRegisters

namespace OAI

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def copyPorts (source target : Fin 29) (hst : source ≠ target)
    (hs : source ≠ 26) (ht : target ≠ 26) : Fin 3 ↪ Fin 29 :=
  ⟨![source, target, 26], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩

def copyProgram (source target : Fin 29) (hst : source ≠ target)
    (hs : source ≠ 26) (ht : target ≠ 26) : Program 29 :=
  KS.W01.FixedCopy.program (copyPorts source target hst hs ht)

theorem copy_spec (source target : Fin 29) (hst : source ≠ target)
    (hs : source ≠ 26) (ht : target ≠ 26) (s : Fin 29 → List Bool)
    (hdst : s target = []) (hscratch : s 26 = []) :
    RunSpec (copyProgram source target hst hs ht) s (put s target (s source))
      (2 * (s source).length + 2) := by
  intro bits hbits
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W01.FixedCopy.machine (copyPorts source target hst hs ht)) _ bits).trans ?_
  exact KS.W01.FixedCopy.run_copy_restore (copyPorts source target hst hs ht)
    s (s source) bits rfl hdst hscratch hbits

def readPorts : Fin 8 ↪ Fin 29 := ⟨![0, 1, 2, 3, 4, 5, 6, 19], by decide⟩
def readProgram : Program 29 := KS.W29.FixedSequential.liftPorts KS.W08.MatrixRead.program readPorts

def readBefore (s : Fin 29 → List Bool) (col row dim : List Bool) : Fin 29 → List Bool :=
  put (put (put s 0 col) 1 row) 2 dim

theorem read_spec {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (i j : Fin n) (s : Fin 29 → List Bool)
    (hsource : s 19 = KS.W08.denseMatrixTape M)
    (hclear : ∀ r : Fin 7, s ⟨r.val, by omega⟩ = []) :
    RunSpec readProgram
      (readBefore s (Computability.encodeNat j.val) (Computability.encodeNat i.val)
        (Computability.encodeNat n))
      (put s 0 (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i j)))
      (1024 * (n + 1) ^ 2 * (b + 1)) := by
  have hsmall : RunSpec KS.W08.MatrixRead.program
      (KS.W08.MatrixRead.workspace (KS.W08.denseMatrixTape M)
        (Computability.encodeNat j.val) (Computability.encodeNat i.val)
        (Computability.encodeNat n) [])
      (KS.W08.MatrixRead.workspace (KS.W08.denseMatrixTape M)
        (KS.W01.encodeRat (KS.W07.DenseRatMatrix.decode M i j)) [] [] [])
      (1024 * (n + 1) ^ 2 * (b + 1)) := by
    intro bits hbits
    exact KS.W08.MatrixRead.run_matrix_read M b hnum hden i j bits hbits.ge
  have hclearPhysical : ∀ r : Fin 29, r.val < 7 → s r = [] := by
    intro r hr
    exact hclear ⟨r.val, hr⟩
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ hsmall
  · intro r
    fin_cases r <;>
      simp [readBefore, put, readPorts, KS.W08.MatrixRead.workspace, hsource]
    all_goals exact hclearPhysical _ (by decide)
  · intro r
    fin_cases r <;> simp [put, readPorts, KS.W08.MatrixRead.workspace, hsource]
    all_goals exact hclearPhysical _ (by decide)
  · intro r hr
    have h0 : r ≠ 0 := hr 0
    have h1 : r ≠ 1 := hr 1
    have h2 : r ≠ 2 := hr 2
    simp [put, readBefore, h0, h1, h2]

def decodePorts : Fin 3 ↪ Fin 29 := ⟨![23, 27, 26], by decide⟩
def decodeProgram : Program 29 := KS.W11.FrameWireCodec.unframeProgram decodePorts

theorem decode_spec (s : Fin 29 → List Bool) (payload tail : List Bool)
    (hs : s 23 = KS.W01.frame payload ++ tail) (hq : s 27 = []) (ht : s 26 = []) :
    RunSpec decodeProgram s (put (put s 23 tail) 27 payload) (3 * payload.length + 2) := by
  convert KS.W11.FrameWireCodec.unframe_spec decodePorts s payload tail using 1 <;> (try rfl) <;>
    funext j <;> fin_cases j <;>
    simp [put, KS.W28.FixedPositiveSerializer.registers, decodePorts, hs, hq, ht]

def framePorts : Fin 3 ↪ Fin 29 := ⟨![4, 28, 26], by decide⟩
def frameProgram : Program 29 := KS.W11.FrameWireCodec.frameProgram framePorts

theorem frame_spec (s : Fin 29 → List Bool) (h4 : s 4 = []) (ht : s 26 = []) :
    RunSpec frameProgram s (put s 28 (KS.W01.frame (s 28))) (4 * (s 28).length + 3) := by
  convert KS.W11.FrameWireCodec.frame_spec framePorts s (s 28) using 1 <;> (try rfl) <;>
    funext j <;> fin_cases j <;>
    simp [put, KS.W28.FixedPositiveSerializer.registers, framePorts, h4, ht]

def appendProgram : Program 29 := KS.W04.BinaryStackMoves.moveProgram 28 25

theorem append_spec (s : Fin 29 → List Bool) :
    RunSpec appendProgram s (put (put s 28 []) 25 ((s 28).reverse ++ s 25))
      ((s 28).length + 1) := by
  convert KS.W15.RationalMultiply.move_spec (28 : Fin 29) 25 (by decide) s using 1 <;> (try rfl)
  funext j
  fin_cases j <;> simp [put, KS.W15.RationalMultiply.moveAfter]

end KS.W12.RowDot

end OAI
