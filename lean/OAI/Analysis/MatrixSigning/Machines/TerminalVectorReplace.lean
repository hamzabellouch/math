import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.NegativeWitness
import OAI.Analysis.MatrixSigning.Encoding.WireProgramPrimitives
import OAI.Analysis.MatrixSigning.Matrices.RowDotModel
import OAI.Analysis.MatrixSigning.Machines.TerminalZeroVector
import OAI.Analysis.MatrixSigning.Encoding.FramedArrayReplacementPorts

namespace OAI

namespace KS.W19.TerminalVectorReplace
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators Matrix

def ports : Fin 5 ↪ Fin 35 := ⟨![23,0,1,2,3], by decide⟩
def program : Program 35 := KS.W11.FramedArrayRewrite.liftedProgram ports

def prepared (s : Fin 35 → List Bool) (new : List Bool) (i : ℕ) : Fin 35 → List Bool :=
  Function.update (Function.update s 0 (KS.W01.frame new)) 3 (List.replicate i true)

theorem replace_spec (s : Fin 35 → List Bool) (xs : List (List Bool)) (i : ℕ)
    (hi : i < xs.length) (new : List Bool) (hs : s 23 = xs.flatMap KS.W01.frame)
    (h0 : s 0 = []) (h1 : s 1 = []) (h2 : s 2 = []) (h3 : s 3 = []) :
    RunSpec program (prepared s new i)
      (Function.update s 23 ((xs.set i new).flatMap KS.W01.frame))
      (2*(xs.flatMap KS.W01.frame).length + 2*(KS.W01.frame new).length+i+3) := by
  have hsmall : RunSpec KS.W11.FramedArrayRewrite.program
      (KS.W11.FramedArrayRewrite.«stacks» (xs.flatMap KS.W01.frame)
        (KS.W01.frame new) [] [] (List.replicate i true))
      (KS.W11.FramedArrayRewrite.«stacks» ((xs.set i new).flatMap KS.W01.frame) [] [] [] [])
      (2*(xs.flatMap KS.W01.frame).length+2*(KS.W01.frame new).length+i+3) := by
    intro bits hb
    have h := KS.W11.FramedArrayRewrite.run_replace xs i hi new [] bits (by simpa using hb.ge)
    simp only [List.append_nil] at h
    exact h
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ ports _ _ _ _ _ hsmall
  · intro j; fin_cases j <;> simp [ports,prepared,KS.W11.FramedArrayRewrite.«stacks»,hs,h1,h2]
  · intro j; fin_cases j <;> simp [ports,KS.W11.FramedArrayRewrite.«stacks»,h0,h1,h2,h3]
  · intro j hj
    have ha := hj 0
    have hb := hj 1
    have hc := hj 4
    change j ≠ 23 at ha
    change j ≠ 0 at hb
    change j ≠ 3 at hc
    simp [prepared,Function.update_of_ne,ha,hb,hc]

def zeroPayloads (n : ℕ) : List (List Bool) := List.replicate n (KS.W01.encodeRat 0)
def unitPayloads (n : ℕ) : List (List Bool) := (zeroPayloads n).set 0 (KS.W01.encodeRat 1)

theorem zeroTape_eq (n : ℕ) : KS.W11.ZeroArrayConstructor.zeroTape n =
    (zeroPayloads n).flatMap KS.W01.frame := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [KS.W11.ZeroArrayConstructor.zeroTape_succ, ih]
    simp only [zeroPayloads, List.replicate_succ, List.flatMap_cons,
      KS.W11.ZeroArrayConstructor.zeroFrame]

def oneFrame : List Bool := KS.W01.frame (KS.W01.encodeRat 1)
def unitProgram : Program 35 := compose TerminalZeroVector.program
  (compose (KS.W15.WireProgram.literalProgram 0 oneFrame) program)

theorem unit_spec (s : Fin 35 → List Bool) (n : ℕ) (hn : 0 < n)
    (hd : s 26 = Computability.encodeNat n)
    (h0 : s 0 = []) (h1 : s 1 = []) (h2 : s 2 = []) (h3 : s 3 = [])
    (h16 : s 16 = []) (h23 : s 23 = []) :
    RunSpec unitProgram s
      (Function.update s 23 ((unitPayloads n).flatMap KS.W01.frame))
      (TerminalZeroVector.ticks n + (oneFrame.length+1+
        (2*((zeroPayloads n).flatMap KS.W01.frame).length+2*oneFrame.length+3))) := by
  have hz := TerminalZeroVector.zero_vector_spec s n hd h0 h1 h2 h16 h23
  rw [zeroTape_eq] at hz
  let mid := Function.update s 23 ((zeroPayloads n).flatMap KS.W01.frame)
  have hl := KS.W15.WireProgram.literal_spec (0 : Fin 35) oneFrame mid
  have hp := replace_spec mid (zeroPayloads n) 0 (by simpa [zeroPayloads] using hn)
    (KS.W01.encodeRat 1) rfl (by simpa [mid] using h0) (by simpa [mid] using h1)
    (by simpa [mid] using h2) (by simpa [mid] using h3)
  have he : Function.update mid 0 (oneFrame ++ mid 0) = prepared mid (KS.W01.encodeRat 1) 0 := by
    funext j; fin_cases j <;> simp [mid,prepared,oneFrame,h0,h3]
  rw [he] at hl
  have ho : Function.update mid 23 (((zeroPayloads n).set 0 (KS.W01.encodeRat 1)).flatMap KS.W01.frame) =
      Function.update s 23 ((unitPayloads n).flatMap KS.W01.frame) := by
    simp [mid,unitPayloads]
  rw [ho] at hp
  exact hz.compose (hl.compose hp)

theorem unit_tape (n : ℕ) :
    ((unitPayloads (n+1)).flatMap KS.W01.frame) =
      KS.W12.RowDot.vectorTape (Pi.single (0 : Fin (n+1)) (1 : ℚ)) := by
  simp [unitPayloads,zeroPayloads,KS.W12.RowDot.vectorTape,List.replicate_succ,
    List.ofFn_succ,Pi.single_apply,List.ofFn_const]

theorem unit_witness_spec {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (s : Fin 35 → List Bool) (hm : M 0 0 < 0)
    (hd : s 26 = Computability.encodeNat (n+1))
    (h0 : s 0 = []) (h1 : s 1 = []) (h2 : s 2 = []) (h3 : s 3 = [])
    (h16 : s 16 = []) (h23 : s 23 = []) :
    RunSpec unitProgram s
      (Function.update s 23 (KS.W12.RowDot.vectorTape (Pi.single (0 : Fin (n+1)) (1 : ℚ))))
      (TerminalZeroVector.ticks (n+1) + (oneFrame.length+1+
        (2*((zeroPayloads (n+1)).flatMap KS.W01.frame).length+2*oneFrame.length+3))) ∧
      dotProduct (Pi.single (0 : Fin (n+1)) (1 : ℚ))
        (M *ᵥ Pi.single (0 : Fin (n+1)) (1 : ℚ)) < 0 := by
  constructor
  · simpa only [unit_tape] using unit_spec s (n+1) (by omega) hd h0 h1 h2 h3 h16 h23
  · exact KS.W17.negativeDiagonal_witness M 0 hm

end KS.W19.TerminalVectorReplace

end OAI
