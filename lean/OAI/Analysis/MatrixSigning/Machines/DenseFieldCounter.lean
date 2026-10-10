import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FiniteControl
import OAI.Analysis.MatrixSigning.Machines.StackTransferSpecs
import OAI.Analysis.MatrixSigning.Machines.InputHeaderPrimitives
import OAI.Analysis.MatrixSigning.Machines.LiteralProgram

namespace OAI

namespace CurrentKS.DenseFieldCounter
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W03.InputHeaderPrimitives

def unary (n : ℕ) : List Bool := List.replicate n true

def state (template remaining work scratch acc unused input : List Bool) : Fin 7 → List Bool :=
  ![template,remaining,work,scratch,acc,unused,input]

def unaryPorts : Fin 3 ↪ Fin 7 := ⟨![6,0,3],by decide⟩
def countPorts : Fin 3 ↪ Fin 7 := ⟨![0,1,3],by decide⟩
def bodyCopyPorts : Fin 3 ↪ Fin 7 := ⟨![0,2,3],by decide⟩
def doublePorts : Fin 3 ↪ Fin 7 := ⟨![4,2,3],by decide⟩
def decode : Program 7 := unaryProgram unaryPorts
def countCopy : Program 7 := KS.W01.FixedCopy.program countPorts
def bodyCopy : Program 7 := KS.W01.FixedCopy.program bodyCopyPorts
def movePart : Program 7 := KS.W04.BinaryStackMoves.moveProgram 2 4
def popCount : Program 7 := KS.W23.LiteralProgram.pop 1
def body : Program 7 := compose bodyCopy (compose movePart popCount)
def square : Program 7 := FiniteControl.whileNonempty 1 body
def doubleCopy : Program 7 := KS.W01.FixedCopy.program doublePorts
def clear : Program 7 := KS.W04.BinaryStackMoves.clearProgram 0
def program : Program 7 := compose decode (compose countCopy
  (compose square (compose doubleCopy (compose movePart clear))))

lemma base_decode_spec (d : ℕ) :
    RunSpec KS.W03.BinaryToUnary.program ![Computability.encodeNat d,[],[]]
      ![[],unary d,[]] (4*d+4*(Computability.encodeNat d).length+2) := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hbits
  have h := KS.W03.BinaryToUnary.run_input_linear (Computability.encodeNat d) bits
    (by rw [KS.W19.bitsValue_encodeNat];omega)
  rw [KS.W03.BinaryToUnary.init_eq] at h
  simp only [KS.W19.bitsValue_encodeNat,unary] at h ⊢
  exact h

lemma decode_spec (d : ℕ) :
    RunSpec decode (state [] [] [] [] [] [] (Computability.encodeNat d))
      (state (unary d) [] [] [] [] [] [])
      (4*d+4*(Computability.encodeNat d).length+2) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec KS.W03.BinaryToUnary.program unaryPorts
    _ _ _ _ _ (base_decode_spec d)
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro j hj
    fin_cases j <;> simp [state]
    · exact False.elim (hj 1 rfl)
    · exact False.elim (hj 0 rfl)

lemma countCopy_spec (d : ℕ) :
    RunSpec countCopy (state (unary d) [] [] [] [] [] [])
      (state (unary d) (unary d) [] [] [] [] []) (2*d+2) := by
  have h := copy_spec countPorts (state (unary d) [] [] [] [] [] []) (unary d) rfl rfl rfl
  convert h using 1 <;> (try rfl)
  · funext j; fin_cases j <;> simp [state,countPorts,Function.update]
  · simp [unary]

lemma bodyCopy_spec (d n : ℕ) (acc : List Bool) :
    RunSpec bodyCopy (state (unary d) (unary n) [] [] acc [] [])
      (state (unary d) (unary n) (unary d) [] acc [] []) (2*d+2) := by
  have h := copy_spec bodyCopyPorts (state (unary d) (unary n) [] [] acc [] [])
    (unary d) rfl rfl rfl
  convert h using 1 <;> (try rfl)
  · funext j; fin_cases j <;> simp [state,bodyCopyPorts,Function.update]
  · simp [unary]

lemma movePart_spec (template remaining part acc : List Bool) :
    RunSpec movePart (state template remaining part [] acc [] [])
      (state template remaining [] [] (part.reverse++acc) [] []) (part.length+1) := by
  have h := KS.W15.RationalMultiply.move_spec (2 : Fin 7) 4 (by decide)
    (state template remaining part [] acc [] [])
  convert h using 1 <;> (try rfl)
  funext j
  fin_cases j <;> simp [state,KS.W15.RationalMultiply.moveAfter]

lemma popCount_spec (template acc : List Bool) (n : ℕ) :
    RunSpec popCount (state template (unary (n+1)) [] [] acc [] [])
      (state template (unary n) [] [] acc [] []) 1 := by
  have h := KS.W23.LiteralProgram.pop_spec (1 : Fin 7)
    (state template (unary (n+1)) [] [] acc [] [])
  convert h using 1 <;> (try rfl)
  funext j
  fin_cases j <;> simp [state,unary,Function.update]

lemma body_spec (d n : ℕ) (acc : List Bool) :
    RunSpec body (state (unary d) (unary (n+1)) [] [] acc [] [])
      (state (unary d) (unary n) [] [] (unary d++acc) [] []) (3*d+4) := by
  have h := (bodyCopy_spec d (n+1) acc).compose
    ((movePart_spec (unary d) (unary (n+1)) (unary d) acc).compose
      (popCount_spec (unary d) ((unary d).reverse++acc) n))
  have ht : (2*d+2)+((unary d).length+1+1)=3*d+4 := by simp [unary];omega
  rw [ht] at h
  simp only [unary,List.reverse_replicate] at h ⊢
  exact h

lemma square_trace (d n : ℕ) (acc : List Bool) :
    FiniteControl.Trace (1 : Fin 7) body
      (state (unary d) (unary n) [] [] acc [] [])
      (state (unary d) [] [] [] (unary (n*d)++acc) [] []) (n*(3*d+5)+1) := by
  induction n generalizing acc with
  | zero =>
    simpa [unary] using (FiniteControl.Trace.stop (body := body) (port := (1 : Fin 7))
      (state (unary d) [] [] [] acc [] []) rfl)
  | succ n ih =>
    have h := FiniteControl.Trace.step
      (show state (unary d) (unary (n+1)) [] [] acc [] [] (1 : Fin 7) ≠ [] by simp [state,unary])
      (body_spec d n acc) (ih (unary d++acc))
    have ht : (3*d+4)+(n*(3*d+5)+1)+1=(n+1)*(3*d+5)+1 := by ring
    rw [ht] at h
    have he : unary (n*d)++(unary d++acc) = unary ((n+1)*d)++acc := by
      rw [←List.append_assoc]
      change (List.replicate (n*d) true++List.replicate d true)++acc = _
      rw [←List.replicate_add]
      have hm : n*d+d=(n+1)*d := by ring
      rw [hm]
      rfl
    rw [he] at h
    exact h

lemma doubleCopy_spec (d n : ℕ) :
    RunSpec doubleCopy (state (unary d) [] [] [] (unary n) [] [])
      (state (unary d) [] (unary n) [] (unary n) [] []) (2*n+2) := by
  have h := copy_spec doublePorts (state (unary d) [] [] [] (unary n) [] [])
    (unary n) rfl rfl rfl
  convert h using 1 <;> (try rfl)
  · funext j; fin_cases j <;> simp [state,doublePorts,Function.update]
  · simp [unary]

lemma clear_spec (d : ℕ) (acc : List Bool) :
    RunSpec clear (state (unary d) [] [] [] acc [] [])
      (state [] [] [] [] acc [] []) (d+1) := by
  have h := KS.W15.RationalMultiply.clear_spec (0 : Fin 7) (state (unary d) [] [] [] acc [] [])
  convert h using 1 <;> (try rfl)
  · funext j; fin_cases j <;> simp [state,KS.W15.RationalMultiply.clearAfter]
  · simp [unary,state]

theorem program_spec (d : ℕ) :
    RunSpec program (state [] [] [] [] [] [] (Computability.encodeNat d))
      (state [] [] [] [] (unary (2*d*d)) [] [])
      (6*d*d+12*d+4*(Computability.encodeNat d).length+9) := by
  have hs := FiniteControl.trace_spec (square_trace d d [])
  simp only [List.append_nil] at hs
  have hm := movePart_spec (unary d) [] (unary (d*d)) (unary (d*d))
  have he : (unary (d*d)).reverse++unary (d*d)=unary (2*d*d) := by
    simp only [unary,List.reverse_replicate,←List.replicate_add]
    congr 1
    ring
  rw [he] at hm
  have h := (decode_spec d).compose ((countCopy_spec d).compose
    (hs.compose ((doubleCopy_spec d (d*d)).compose
      (hm.compose (clear_spec d (unary (2*d*d)))))))
  have ht : (4*d+4*(Computability.encodeNat d).length+2)+
      ((2*d+2)+((d*(3*d+5)+1)+((2*(d*d)+2)+((unary (d*d)).length+1+(d+1))))) =
      6*d*d+12*d+4*(Computability.encodeNat d).length+9 := by
    simp only [unary,List.length_replicate]
    ring
  rw [ht] at h
  exact h

end CurrentKS.DenseFieldCounter

end OAI
