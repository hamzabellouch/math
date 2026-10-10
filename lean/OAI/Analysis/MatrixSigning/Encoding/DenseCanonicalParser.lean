import Mathlib
import OAI.Analysis.MatrixSigning.Machines.DenseFieldCounter
import OAI.Analysis.MatrixSigning.Realization.DenseInputArrays

namespace OAI

namespace CurrentKS.DenseCanonicalParser
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def state (source value template dim count saved : List Bool) : Fin 21 → List Bool :=
  fun j => if j=13 then source else if j=10 then value else if j=17 then template
    else if j=18 then dim else if j=19 then count else if j=20 then saved else []

def headerPorts : Fin 5 ↪ Fin 21 := ⟨![13,18,19,0,10],by decide⟩
def copyPorts : Fin 3 ↪ Fin 21 := ⟨![18,20,0],by decide⟩
def counterPorts : Fin 7 ↪ Fin 21 := ⟨![0,1,2,3,17,4,18],by decide⟩
def matrixPorts : Fin 18 ↪ Fin 21 := ⟨Fin.castAdd 3,Fin.castAdd_injective 18 3⟩
def header : Program 21 := liftPorts DenseInputMachine.readHeader headerPorts
def saveDimension : Program 21 := KS.W01.FixedCopy.program copyPorts
def counter : Program 21 := liftPorts DenseFieldCounter.program counterPorts
def matrices : Program 21 := liftPorts RawMatrixMachine.program matrixPorts
def body : Program 21 := compose saveDimension (compose counter matrices)
def program : Program 21 := compose header body

lemma header_spec (x : Input) :
    RunSpec header (state x.encode [] [] [] [] [])
      (state (DenseInputMachine.denseTape x) [] []
        (Computability.encodeNat x.d) (Computability.encodeNat x.N) [])
      (DenseInputMachine.headerTicks x.d x.N) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ headerPorts _ _ _ _ _
    (DenseInputMachine.readHeader_spec x [])
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro j hj
    have h13 : j≠13 := hj 0
    have h18 : j≠18 := hj 1
    have h19 : j≠19 := hj 2
    simp [state,h13,h18,h19]

lemma saveDimension_spec (source dim count : List Bool) :
    RunSpec saveDimension (state source [] [] dim count [])
      (state source [] [] dim count dim) (2*dim.length+2) := by
  have h := KS.W03.InputHeaderPrimitives.copy_spec copyPorts
    (state source [] [] dim count []) dim rfl rfl rfl
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [state,copyPorts,Function.update]

lemma counter_spec (source count : List Bool) (d : ℕ) :
    RunSpec counter (state source [] [] (Computability.encodeNat d) count (Computability.encodeNat d))
      (state source [] (DenseFieldCounter.unary (2*d*d)) [] count (Computability.encodeNat d))
      (6*d*d+12*d+4*(Computability.encodeNat d).length+9) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ counterPorts _ _ _ _ _
    (DenseFieldCounter.program_spec d)
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro j hj
    have h17 : j≠17 := hj 4
    have h18 : j≠18 := hj 6
    simp [state,h17,h18]

lemma matrices_spec (x : Input) :
    RunSpec matrices
      (state (DenseInputMachine.denseTape x) [] (DenseFieldCounter.unary (2*x.d*x.d)) []
        (Computability.encodeNat x.N) (Computability.encodeNat x.d))
      (state [] (DenseInputArrays.canonical x) (DenseFieldCounter.unary (2*x.d*x.d)) []
        (Computability.encodeNat x.N) (Computability.encodeNat x.d))
      ((x.N*(600*(x.length+1)^4+1)+1)+(DenseInputArrays.canonical x).length+1) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ matrixPorts _ _ _ _ _
    (DenseInputArrays.canonical_scan_spec x)
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro j hj
    have h13 : j≠13 := hj 13
    have h10 : j≠10 := hj 10
    simp [state,h13,h10]

def ticks (x : Input) : ℕ :=
  DenseInputMachine.headerTicks x.d x.N+(2*(Computability.encodeNat x.d).length+2)+
    (6*x.d*x.d+12*x.d+4*(Computability.encodeNat x.d).length+9)+
    ((x.N*(600*(x.length+1)^4+1)+1)+(DenseInputArrays.canonical x).length+1)

theorem program_spec (x : Input) :
    RunSpec program (state x.encode [] [] [] [] [])
      (state [] (DenseInputArrays.canonical x) (DenseFieldCounter.unary (2*x.d*x.d)) []
        (Computability.encodeNat x.N) (Computability.encodeNat x.d)) (ticks x) := by
  have h := (header_spec x).compose ((saveDimension_spec (DenseInputMachine.denseTape x)
      (Computability.encodeNat x.d) (Computability.encodeNat x.N)).compose
    ((counter_spec (DenseInputMachine.denseTape x) (Computability.encodeNat x.N) x.d).compose
      (matrices_spec x)))
  simp only [ticks,Nat.add_assoc] at h ⊢
  exact h

lemma binaryDimension_le_length (x : Input) : (Computability.encodeNat x.d).length≤x.length := by
  simp only [Input.length,Input.encode,List.length_append,CurrentKS.encodeNat,
    DenseInputMachine.length_frame]
  omega

lemma ticks_le_polynomial (x : Input) (hN : x.N≠0) : ticks x≤700*(x.length+1)^5 := by
  have hH := DenseInputMachine.headerTicks_le x
  have hD := DenseInputArrays.dimension_le_length x hN
  have hD2 := DenseInputArrays.dimension_sq_le_length x hN
  have hB := binaryDimension_le_length x
  have hP := DenseInputArrays.canonical_scan_polynomial x
  unfold ticks
  nlinarith [Nat.zero_le (x.length^2),Nat.zero_le (x.length^3),
    Nat.zero_le (x.length^4),Nat.zero_le (x.length^5)]

end CurrentKS.DenseCanonicalParser

end OAI
