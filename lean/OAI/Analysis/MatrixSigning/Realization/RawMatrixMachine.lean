import Mathlib
import OAI.Analysis.MatrixSigning.Machines.InputHeaderPrimitives
import OAI.Analysis.MatrixSigning.Realization.RawRationalArrayMachine

namespace OAI

namespace CurrentKS.RawMatrixMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W01

abbrev unary := RawRationalArrayMachine.unary

def extend (s : Fin 16 → List Bool) (acc template : List Bool) : Fin 18 → List Bool :=
  fun j => if hj : j.val < 16 then s ⟨j.val,hj⟩ else if j.val=16 then acc else template

def state (source value count acc template : List Bool) : Fin 18 → List Bool :=
  extend (RawRationalArrayMachine.state source value [] count) acc template

def ports : Fin 16 ↪ Fin 18 := ⟨Fin.castAdd 2,Fin.castAdd_injective 16 2⟩
def fields : Program 18 := liftPorts RawRationalArrayMachine.program ports
def popMarker : Program 18 := KS.W23.LiteralProgram.pop 13
def copyPorts : Fin 3 ↪ Fin 18 := ⟨![17,15,1],by decide⟩
def copyCount : Program 18 := KS.W01.FixedCopy.program copyPorts
def framePorts : Fin 3 ↪ Fin 18 := ⟨![0,10,1],by decide⟩
def framing : Program 18 := KS.W11.FrameWireCodec.frameProgram framePorts
def appendFrame : Program 18 := KS.W04.BinaryStackMoves.moveProgram 10 16
def body : Program 18 := compose popMarker (compose copyCount
  (compose fields (compose framing appendFrame)))
def scan : Program 18 := FiniteControl.whileNonempty 13 body
def finish : Program 18 := KS.W04.BinaryStackMoves.moveProgram 16 10
def program : Program 18 := compose scan finish

def rawTape (matrices : List (List RationalEntry)) : List Bool :=
  matrices.flatMap (fun a => true :: RawRationalArrayMachine.rawTape a)
def canonicalTape (matrices : List (List RationalEntry)) : List Bool :=
  matrices.flatMap (fun a => KS.W01.frame (RawRationalArrayMachine.canonicalTape a))

@[simp] lemma extend_port (s : Fin 16 → List Bool) (acc template : List Bool) (i : Fin 16) :
    extend s acc template (ports i)=s i := by simp [extend,ports]

lemma extend_other (s t : Fin 16 → List Bool) (acc template : List Bool)
    (j : Fin 18) (hj : ∀ i,j ≠ ports i) :
    extend t acc template j=extend s acc template j := by
  by_cases h : j.val<16
  · exact (hj ⟨j.val,h⟩ (Fin.ext rfl)).elim
  · simp [extend,h]

lemma fields_spec (a : List RationalEntry) (tail acc template : List Bool) :
    RunSpec fields
      (state (RawRationalArrayMachine.rawTape a++tail) [] (unary a.length) acc template)
      (state tail (RawRationalArrayMachine.canonicalTape a) [] acc template)
      (500*((RawRationalArrayMachine.rawTape a).length+1)^4) := by
  exact KS.W01.FixedPortRunSpec.lift_runSpec _ ports _ _ _ _ _
    (RawRationalArrayMachine.polynomial_spec a tail)
    (extend_port _ _ _) (extend_port _ _ _) (extend_other _ _ _ _)

lemma popMarker_spec (source acc template : List Bool) :
    RunSpec popMarker (state (true::source) [] [] acc template)
      (state source [] [] acc template) 1 := by
  have h := KS.W23.LiteralProgram.pop_spec (13 : Fin 18) (state (true::source) [] [] acc template)
  convert h using 1 <;> (try rfl)
  funext index
  fin_cases index <;> simp [state,extend,RawRationalArrayMachine.state,
    RawRationalArrayMachine.extend,RawRationalMachine.state,Function.update]

lemma copyCount_spec (source acc template : List Bool) :
    RunSpec copyCount (state source [] [] acc template)
      (state source [] template acc template) (2*template.length+2) := by
  have h := KS.W03.InputHeaderPrimitives.copy_spec copyPorts
    (state source [] [] acc template) template rfl rfl rfl
  convert h using 1 <;> (try rfl)
  funext index
  fin_cases index <;> simp [state,extend,RawRationalArrayMachine.state,
    RawRationalArrayMachine.extend,RawRationalMachine.state,copyPorts,Function.update]

lemma framing_spec (source value acc template : List Bool) :
    RunSpec framing (state source value [] acc template)
      (state source (KS.W01.frame value) [] acc template) (4*value.length+3) := by
  have h := KS.W11.FrameWireCodec.frame_spec framePorts (state source [] [] acc template) value
  convert h using 1 <;> (try rfl) <;> funext j <;> fin_cases j <;> simp [state,extend,RawRationalArrayMachine.state,
    RawRationalArrayMachine.extend,RawRationalMachine.state,framePorts,
    KS.W28.FixedPositiveSerializer.registers]

lemma appendFrame_spec (source value acc template : List Bool) :
    RunSpec appendFrame (state source value [] acc template)
      (state source [] [] (value.reverse++acc) template) (value.length+1) := by
  have h := KS.W15.RationalMultiply.move_spec (10 : Fin 18) 16 (by decide)
    (state source value [] acc template)
  convert h using 1 <;> (try rfl)
  funext index
  fin_cases index <;> simp [state,extend,RawRationalArrayMachine.state,
    RawRationalArrayMachine.extend,RawRationalMachine.state,KS.W15.RationalMultiply.moveAfter]

def bodyTicks (a : List RationalEntry) : ℕ :=
  1+(2*a.length+2)+(500*((RawRationalArrayMachine.rawTape a).length+1)^4)+
    (4*(RawRationalArrayMachine.canonicalTape a).length+3)+
    ((KS.W01.frame (RawRationalArrayMachine.canonicalTape a)).length+1)

lemma body_spec (a : List RationalEntry) (tail acc : List Bool) :
    RunSpec body
      (state (true::(RawRationalArrayMachine.rawTape a++tail)) [] [] acc (unary a.length))
      (state tail [] [] ((KS.W01.frame (RawRationalArrayMachine.canonicalTape a)).reverse++acc)
        (unary a.length)) (bodyTicks a) := by
  have h := (popMarker_spec (RawRationalArrayMachine.rawTape a++tail) acc (unary a.length)).compose
    ((copyCount_spec (RawRationalArrayMachine.rawTape a++tail) acc (unary a.length)).compose
      ((fields_spec a tail acc (unary a.length)).compose
        ((framing_spec tail (RawRationalArrayMachine.canonicalTape a) acc (unary a.length)).compose
          (appendFrame_spec tail (KS.W01.frame (RawRationalArrayMachine.canonicalTape a)) acc
            (unary a.length)))))
  simp only [bodyTicks,unary,RawRationalArrayMachine.unary,List.length_replicate,Nat.add_assoc] at h ⊢
  exact h

lemma bodyTicks_le (a : List RationalEntry) (L : ℕ)
    (hL : (RawRationalArrayMachine.rawTape a).length ≤ L) : bodyTicks a ≤ 600*(L+1)^4 := by
  have hn := (RawRationalArrayMachine.count_le_raw a).trans hL
  have hv := (RawRationalArrayMachine.canonical_length_le a).trans (Nat.mul_le_mul_left 4 hL)
  have hp : ((RawRationalArrayMachine.rawTape a).length+1)^4 ≤ (L+1)^4 := Nat.pow_le_pow_left (by omega) _
  simp only [bodyTicks,length_frame]
  nlinarith [Nat.zero_le (L^2),Nat.zero_le (L^3),Nat.zero_le (L^4)]

lemma scan_trace (matrices : List (List RationalEntry)) (K L : ℕ) (acc : List Bool)
    (hK : ∀ a ∈ matrices,a.length=K)
    (hL : ∀ a ∈ matrices,(RawRationalArrayMachine.rawTape a).length ≤ L) :
    FiniteControl.Trace (13 : Fin 18) body (state (rawTape matrices) [] [] acc (unary K))
      (state [] [] [] ((canonicalTape matrices).reverse++acc) (unary K))
      (matrices.length*(600*(L+1)^4+1)+1) := by
  induction matrices generalizing acc with
  | nil =>
    simpa [rawTape,canonicalTape] using (FiniteControl.Trace.stop (body := body) (port := (13 : Fin 18))
      (state [] [] [] acc (unary K)) (by simp [state,extend,RawRationalArrayMachine.state,
        RawRationalArrayMachine.extend,RawRationalMachine.state]))
  | cons a as ih =>
    have ha := hK a (by simp)
    have hb := (body_spec a (rawTape as) acc).mono (bodyTicks_le a L (hL a (by simp)))
    rw [ha] at hb
    have ht := ih ((KS.W01.frame (RawRationalArrayMachine.canonicalTape a)).reverse++acc)
      (fun b hb => hK b (by simp [hb])) (fun b hb => hL b (by simp [hb]))
    have hs : state (true::(RawRationalArrayMachine.rawTape a++rawTape as)) [] [] acc
        (unary K) (13 : Fin 18) ≠ [] := by
      simp [state,extend,RawRationalArrayMachine.state,RawRationalArrayMachine.extend,
        RawRationalMachine.state]
    have h := FiniteControl.Trace.step hs hb ht
    have hc : 600*(L+1)^4+(as.length*(600*(L+1)^4+1)+1)+1 =
        (as.length+1)*(600*(L+1)^4+1)+1 := by ring
    rw [hc] at h
    simpa only [rawTape,List.flatMap_cons,List.cons_append,canonicalTape,List.reverse_append,
      List.append_assoc,List.length_cons] using h

lemma finish_spec (word template : List Bool) :
    RunSpec finish (state [] [] [] word.reverse template) (state [] word [] [] template)
      (word.length+1) := by
  have h := KS.W15.RationalMultiply.move_spec (16 : Fin 18) 10 (by decide)
    (state [] [] [] word.reverse template)
  convert h using 1 <;> (try rfl)
  · funext j
    fin_cases j <;> simp [state,extend,RawRationalArrayMachine.state,
      RawRationalArrayMachine.extend,RawRationalMachine.state,KS.W15.RationalMultiply.moveAfter]
  · simp [state,extend]

theorem program_spec (matrices : List (List RationalEntry)) (K L : ℕ)
    (hK : ∀ a ∈ matrices,a.length=K)
    (hL : ∀ a ∈ matrices,(RawRationalArrayMachine.rawTape a).length ≤ L) :
    RunSpec program (state (rawTape matrices) [] [] [] (unary K))
      (state [] (canonicalTape matrices) [] [] (unary K))
      ((matrices.length*(600*(L+1)^4+1)+1)+(canonicalTape matrices).length+1) := by
  have hs := FiniteControl.trace_spec (scan_trace matrices K L [] hK hL)
  simp only [List.append_nil] at hs
  have h := hs.compose (finish_spec (canonicalTape matrices) (unary K))
  simp only [Nat.add_assoc] at h ⊢
  exact h

end CurrentKS.RawMatrixMachine

end OAI
