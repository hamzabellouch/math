import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.WireAppend
import OAI.Analysis.MatrixSigning.Optimization.TerminalWitnessTapes

namespace OAI

namespace KS.W19.TerminalSparseAssembly
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.TerminalVectorReplace

def unaryPorts : Fin 3 ↪ Fin 35 := ⟨![30,3,1], by decide⟩
def unaryProgram : Program 35 := liftPorts KS.W03.BinaryToUnary.program unaryPorts

def setOneProgram : Program 35 := compose
  (KS.W15.WireProgram.literalProgram 0 oneFrame) (compose unaryProgram TerminalVectorReplace.program)

theorem setOne_spec (s : Fin 35 → List Bool) (xs : List (List Bool)) (j : ℕ)
    (hj : j < xs.length) (hs : s 23 = xs.flatMap KS.W01.frame)
    (hindex : s 30 = Computability.encodeNat j)
    (h0 : s 0 = []) (h1 : s 1 = []) (h2 : s 2 = []) (h3 : s 3 = []) :
    RunSpec setOneProgram s
      (Function.update (Function.update s 30 []) 23 ((xs.set j (KS.W01.encodeRat 1)).flatMap KS.W01.frame))
      (oneFrame.length+1 + ((4*j+4*(Computability.encodeNat j).length+2) +
        (2*(xs.flatMap KS.W01.frame).length+2*oneFrame.length+j+3))) := by
  let base := Function.update s 30 []
  let first := Function.update s 0 oneFrame
  have hl : RunSpec (KS.W15.WireProgram.literalProgram 0 oneFrame) s first (oneFrame.length+1) := by
    simpa [first,h0] using KS.W15.WireProgram.literal_spec (0 : Fin 35) oneFrame s
  have hu0 : RunSpec KS.W03.BinaryToUnary.program
      ![Computability.encodeNat j,[],[]] ![[],List.replicate j true,[]]
      (4*j+4*(Computability.encodeNat j).length+2) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine
    intro bits hb
    have h := KS.W03.BinaryToUnary.run_input_linear (Computability.encodeNat j) bits
      (by simpa only [bitsValue_encodeNat] using hb.ge)
    simp only [KS.W03.BinaryToUnary.init_eq,KS.W03.BinaryToUnary.cfg,
      bitsValue_encodeNat] at h
    exact h
  have hu : RunSpec unaryProgram first (prepared base (KS.W01.encodeRat 1) j)
      (4*j+4*(Computability.encodeNat j).length+2) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ unaryPorts _ _ _ _ _ hu0
    · intro i; fin_cases i <;> simp [unaryPorts,first,hindex,h1,h3]
    · intro i; fin_cases i <;> simp [unaryPorts,base,prepared,h1]
    · intro i hi
      have ha := hi 0
      have hb := hi 1
      change i ≠ 30 at ha
      change i ≠ 3 at hb
      by_cases hi0 : i = 0
      · subst i; simp [first,base,prepared,oneFrame]
      · simp [first,base,prepared,oneFrame,Function.update_of_ne,ha,hb,hi0]
  have hr := replace_spec base xs j hj (KS.W01.encodeRat 1)
    (by simpa [base] using hs) (by simpa [base] using h0) (by simpa [base] using h1)
    (by simpa [base] using h2) (by simpa [base] using h3)
  exact hl.compose (hu.compose hr)

def framePorts : Fin 3 ↪ Fin 35 := ⟨![0,28,1], by decide⟩
def frameProgram : Program 35 := KS.W11.FrameWireCodec.frameProgram framePorts
def headProgram : Program 35 := compose TerminalZeroVector.program
  (compose frameProgram (compose (KS.W07.WireAppend.program 28 0 16) TerminalVectorReplace.program))

def headTicks (n : ℕ) (c : ℚ) : ℕ := TerminalZeroVector.ticks n +
  (4*(KS.W01.encodeRat c).length+3 +
    (2*(KS.W01.frame (KS.W01.encodeRat c)).length+2 +
      (2*((zeroPayloads n).flatMap KS.W01.frame).length+2*(KS.W01.frame (KS.W01.encodeRat c)).length+3)))

theorem head_spec (s : Fin 35 → List Bool) (n : ℕ) (hn : 0<n) (c : ℚ)
    (hd : s 26 = Computability.encodeNat n) (hc : s 28 = KS.W01.encodeRat c)
    (h0 : s 0 = []) (h1 : s 1 = []) (h2 : s 2 = []) (h3 : s 3 = [])
    (h16 : s 16 = []) (h23 : s 23 = []) :
    RunSpec headProgram s
      (Function.update (Function.update s 28 []) 23
        (((zeroPayloads n).set 0 (KS.W01.encodeRat c)).flatMap KS.W01.frame)) (headTicks n c) := by
  let mid := Function.update s 23 ((zeroPayloads n).flatMap KS.W01.frame)
  let base := Function.update mid 28 []
  let framed := Function.update mid 28 (KS.W01.frame (KS.W01.encodeRat c))
  have hz := TerminalZeroVector.zero_vector_spec s n hd h0 h1 h2 h16 h23
  rw [zeroTape_eq] at hz
  have hf := KS.W11.FrameWireCodec.frame_spec framePorts mid (KS.W01.encodeRat c)
  have hi : KS.W28.FixedPositiveSerializer.registers framePorts mid [] (KS.W01.encodeRat c) [] = mid := by
    funext j; fin_cases j <;> simp [framePorts,KS.W28.FixedPositiveSerializer.registers,mid,h0,h1,hc]
  have ho : KS.W28.FixedPositiveSerializer.registers framePorts mid [] (KS.W01.frame (KS.W01.encodeRat c)) [] = framed := by
    funext j; fin_cases j <;> simp [framePorts,KS.W28.FixedPositiveSerializer.registers,mid,framed,h0,h1]
  rw [hi,ho] at hf
  have hm := KS.W07.WireAppend.spec (28 : Fin 35) 0 16 (by decide) (by decide) (by decide)
    framed (by simpa [framed,mid] using h16)
  have he : KS.W07.WireAppend.after 28 0 framed = prepared base (KS.W01.encodeRat c) 0 := by
    funext j; fin_cases j <;> simp [KS.W07.WireAppend.after,framed,mid,base,prepared,h0,h3]
  rw [he] at hm
  have hr := replace_spec base (zeroPayloads n) 0 (by simpa [zeroPayloads] using hn)
    (KS.W01.encodeRat c) (by simp [base,mid]) (by simpa [base,mid] using h0)
    (by simpa [base,mid] using h1) (by simpa [base,mid] using h2) (by simpa [base,mid] using h3)
  have hout : Function.update base 23 (((zeroPayloads n).set 0 (KS.W01.encodeRat c)).flatMap KS.W01.frame) =
      Function.update (Function.update s 28 []) 23
        (((zeroPayloads n).set 0 (KS.W01.encodeRat c)).flatMap KS.W01.frame) := by
    funext j; fin_cases j <;> simp [base,mid]
  rw [hout] at hr
  have h := hz.compose (hf.compose (hm.compose hr))
  simp [headProgram,headTicks,framed,mid] at h ⊢
  exact h

def program : Program 35 := compose headProgram setOneProgram

def ticks (n j : ℕ) (c : ℚ) : ℕ := headTicks n c +
  (oneFrame.length+1 + ((4*j+4*(Computability.encodeNat j).length+2) +
    (2*(((zeroPayloads n).set 0 (KS.W01.encodeRat c)).flatMap KS.W01.frame).length+
      2*oneFrame.length+j+3)))

theorem sparse_spec {n : ℕ} (s : Fin 35 → List Bool) (j : Fin (n+1)) (hj : j ≠ 0) (c : ℚ)
    (hd : s 26 = Computability.encodeNat (n+1)) (hc : s 28 = KS.W01.encodeRat c)
    (hindex : s 30 = Computability.encodeNat j.val)
    (h0 : s 0 = []) (h1 : s 1 = []) (h2 : s 2 = []) (h3 : s 3 = [])
    (h16 : s 16 = []) (h23 : s 23 = []) :
    RunSpec program s
      (Function.update (Function.update (Function.update s 28 []) 30 []) 23
        (KS.W12.RowDot.vectorTape (sparseVector j c))) (ticks (n+1) j.val c) := by
  let xs := (zeroPayloads (n+1)).set 0 (KS.W01.encodeRat c)
  let mid := Function.update (Function.update s 28 []) 23 (xs.flatMap KS.W01.frame)
  have hh := head_spec s (n+1) (by omega) c hd hc h0 h1 h2 h3 h16 h23
  have hi := setOne_spec mid xs j.val (by simpa [xs,zeroPayloads] using j.isLt) rfl
    (by simpa [mid] using hindex) (by simpa [mid] using h0) (by simpa [mid] using h1)
    (by simpa [mid] using h2) (by simpa [mid] using h3)
  have ht : (xs.set j.val (KS.W01.encodeRat 1)).flatMap KS.W01.frame =
      KS.W12.RowDot.vectorTape (sparseVector j c) := sparse_tape j hj c
  rw [ht] at hi
  have he : Function.update (Function.update mid 30 []) 23
      (KS.W12.RowDot.vectorTape (sparseVector j c)) =
      Function.update (Function.update (Function.update s 28 []) 30 []) 23
        (KS.W12.RowDot.vectorTape (sparseVector j c)) := by
    funext k; fin_cases k <;> simp [mid]
  rw [he] at hi
  exact hh.compose hi

end KS.W19.TerminalSparseAssembly

end OAI
