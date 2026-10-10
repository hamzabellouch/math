import Mathlib
import OAI.Analysis.MatrixSigning.Realization.OriginalFieldsRealization
import OAI.Analysis.MatrixSigning.Encoding.DenseCanonicalParser

namespace OAI

namespace CurrentKS.OriginalParserRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine Realization

def state (dim value template count saved : Word) : Fin 21 → Word :=
  fun j => if j=0 then dim else if j=10 then value else if j=17 then template
    else if j=19 then count else if j=20 then saved else []
def start : Program 21 := transfer 0 1 13
def clearTemplate : Program 21 := KS.W04.BinaryStackMoves.clearProgram 17
def clearCount : Program 21 := KS.W04.BinaryStackMoves.clearProgram 19
def unaryPorts : Fin 3 ↪ Fin 21 := ⟨![20,0,1],by decide⟩
def decode : Program 21 := liftPorts KS.W03.BinaryToUnary.program unaryPorts
def framePorts : Fin 3 ↪ Fin 21 := ⟨![1,0,2],by decide⟩
def frameDimension : Program 21 := KS.W11.FrameWireCodec.frameProgram framePorts
def prefixWord : Program 21 := KS.W12.StackTransfer.program 0 10 1
def finish : Program 21 := transfer 10 1 0

def program : Program 21 := compose start (compose DenseCanonicalParser.program
  (compose clearTemplate (compose clearCount (compose decode (compose frameDimension (compose prefixWord finish))))))

lemma start_spec (w : Word) : RunSpec start (io w) (DenseCanonicalParser.state w [] [] [] [] []) (2*w.length+2) := by
  have h := transfer_spec (0 : Fin 21) 1 13 (by decide) (by decide) (by decide) (io w) rfl rfl
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [io,DenseCanonicalParser.state,Function.update]
lemma clearTemplate_spec (v t n d : Word) :
    RunSpec clearTemplate (DenseCanonicalParser.state [] v t [] n d)
      (state [] v [] n d) (t.length+1) := by
  have h := KS.W15.RationalMultiply.clear_spec (17 : Fin 21) (DenseCanonicalParser.state [] v t [] n d)
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [state,DenseCanonicalParser.state,KS.W15.RationalMultiply.clearAfter]
lemma clearCount_spec (v n d : Word) : RunSpec clearCount (state [] v [] n d)
    (state [] v [] [] d) (n.length+1) := by
  have h := KS.W15.RationalMultiply.clear_spec (19 : Fin 21) (state [] v [] n d)
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [state,KS.W15.RationalMultiply.clearAfter]
lemma decode_spec (v : Word) (d : ℕ) : RunSpec decode (state [] v [] [] (Computability.encodeNat d))
    (state (natCode d) v [] [] []) (4*d+4*(Computability.encodeNat d).length+2) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ unaryPorts _ _ _ _ _ (DenseFieldCounter.base_decode_spec d)
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro j hj
    have h0 : j≠0 := hj 1
    have h20 : j≠20 := hj 0
    simp [state,h0,h20]
lemma frameDimension_spec (v w : Word) : RunSpec frameDimension (state w v [] [] [])
    (state (KS.W01.frame w) v [] [] []) (4*w.length+3) := by
  have h := KS.W11.FrameWireCodec.frame_spec framePorts (state [] v [] [] []) w
  convert h using 1 <;> (try rfl) <;> funext j <;> fin_cases j <;>
    simp [state,framePorts,KS.W28.FixedPositiveSerializer.registers]
lemma prefixWord_spec (v w : Word) : RunSpec prefixWord (state w v [] [] [])
    (state [] (w++v) [] [] []) (2*w.length+2) := by
  have h := KS.W12.StackTransfer.spec (0 : Fin 21) 10 1 (by decide) (by decide) (by decide)
    (state w v [] [] []) rfl
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [state,KS.W12.StackTransfer.after]
lemma finish_spec (v : Word) : RunSpec finish (state [] v [] [] []) (io v) (2*v.length+2) := by
  have h := transfer_spec (10 : Fin 21) 1 0 (by decide) (by decide) (by decide) (state [] v [] [] []) rfl rfl
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [state,io,Function.update]

lemma canonical_eq (x : Input) : DenseInputArrays.canonical x=listCode vectorCode (List.ofFn (fieldValues x)) := by
  simp only [DenseInputArrays.canonical,DenseInputArrays.records,RawMatrixMachine.canonicalTape,
    RawRationalArrayMachine.canonicalTape,listCode,FramedMapRoutine.tape,vectorCode]
  simp only [List.flatMap_def,List.map_ofFn,Function.comp_def,fieldValues,List.map_map]

def ticks (x : Input) : ℕ :=
  (2*x.length+2)+DenseCanonicalParser.ticks x+(2*x.d*x.d+1)+((Computability.encodeNat x.N).length+1)+
    (4*x.d+4*(Computability.encodeNat x.d).length+2)+(4*x.d+3)+
    (2*(2*x.d+1)+2)+(2*(originalCode x).length+2)

theorem program_spec (x : Input) : RunSpec program (io x.encode) (io (originalCode x)) (ticks x) := by
  have h := (start_spec x.encode).compose ((DenseCanonicalParser.program_spec x).compose
    ((clearTemplate_spec (DenseInputArrays.canonical x) (DenseFieldCounter.unary (2*x.d*x.d))
      (Computability.encodeNat x.N) (Computability.encodeNat x.d)).compose
    ((clearCount_spec (DenseInputArrays.canonical x) (Computability.encodeNat x.N) (Computability.encodeNat x.d)).compose
    ((decode_spec (DenseInputArrays.canonical x) x.d).compose
    ((frameDimension_spec (DenseInputArrays.canonical x) (natCode x.d)).compose
    ((prefixWord_spec (DenseInputArrays.canonical x) (KS.W01.frame (natCode x.d))).compose
      (finish_spec (KS.W01.frame (natCode x.d)++DenseInputArrays.canonical x))))))))
  have he : KS.W01.frame (natCode x.d)++DenseInputArrays.canonical x=originalCode x := by
    rw [canonical_eq];rfl
  simp only [he,ticks,Input.length,DenseFieldCounter.unary,natCode,List.length_replicate,
    KS.W01.length_frame,Nat.add_assoc] at h ⊢
  exact h

def routine : Routine Input.encode originalCode ticks := ⟨20,program,program_spec⟩

lemma originalCode_length (x : Input) : (originalCode x).length≤2*x.d+1+8*x.length := by
  have h := DenseInputArrays.canonical_length_le_input x
  have he : (originalCode x).length=2*x.d+1+(DenseInputArrays.canonical x).length := by
    rw [canonical_eq]
    change (KS.W01.frame (natCode x.d)++listCode vectorCode (List.ofFn (fieldValues x))).length=_
    simp only [List.length_append,KS.W01.length_frame,natCode,List.length_replicate]
  rw [he];omega
lemma ticks_le (x : Input) (hN : x.N≠0) : ticks x≤800*(x.length+1)^5 := by
  have hD := DenseInputArrays.dimension_le_length x hN
  have hD2 := DenseInputArrays.dimension_sq_le_length x hN
  have hP := DenseCanonicalParser.ticks_le_polynomial x hN
  have hB := DenseCanonicalParser.binaryDimension_le_length x
  have hC := originalCode_length x
  have hN' : (Computability.encodeNat x.N).length≤x.length := by
    simp only [Input.length,Input.encode,List.length_append,CurrentKS.encodeNat,DenseInputMachine.length_frame]
    omega
  unfold ticks
  nlinarith [Nat.zero_le (x.length^2),Nat.zero_le (x.length^3),Nat.zero_le (x.length^4),Nat.zero_le (x.length^5)]

end CurrentKS.OriginalParserRoutine

end OAI
