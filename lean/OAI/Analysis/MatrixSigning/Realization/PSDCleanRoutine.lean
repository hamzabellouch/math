import Mathlib
import OAI.Analysis.MatrixSigning.Realization.CleanRoutine
import OAI.Analysis.MatrixSigning.Realization.RoutineLength
import OAI.Analysis.MatrixSigning.Complexity.PSDControllerPolynomial

namespace OAI

namespace CurrentKS.PSDCleanRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W07 KS.W17 KS.W17.FixedPSD
open CleanRoutine

abbrev Datum := Σ n : ℕ,DenseRatMatrix n

def input (a : Datum) : Word :=
  KS.W01.frame (Computability.encodeNat a.1)++KS.W08.denseMatrixTape a.2
def output (a : Datum) : Word :=
  (rationalNegativeWitness a.1 (DenseRatMatrix.decode a.2)).elim [] KS.W12.RowDot.vectorTape

def parsed (dimension data : Word) : Fin 35 → Word :=
  fun j => if j=26 then dimension else if j=0 then data else []
def decode : Program 35 := KS.W11.FrameWireCodec.unframeProgram ⟨![0,26,34],by decide⟩
def install : Program 35 := CleanRoutine.transfer 0 34 31
def extract : Program 35 := CleanRoutine.transfer 23 34 0
def program : Program 35 := compose decode (compose install (compose controllerProgram extract))

lemma decode_spec (a : Datum) : RunSpec decode (io (input a))
    (parsed (Computability.encodeNat a.1) (KS.W08.denseMatrixTape a.2))
    (3*(Computability.encodeNat a.1).length+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec
    (⟨![0,26,34],by decide⟩ : Fin 3 ↪ Fin 35) (fun _ => [])
    (Computability.encodeNat a.1) (KS.W08.denseMatrixTape a.2)
  convert h using 1 <;> (try rfl) <;> funext j <;> fin_cases j <;> rfl

lemma install_spec (a : Datum) : RunSpec install
    (parsed (Computability.encodeNat a.1) (KS.W08.denseMatrixTape a.2)) (matrixState [] a.2)
    (2*(KS.W08.denseMatrixTape a.2).length+2) := by
  have h := CleanRoutine.transfer_spec (0 : Fin 35) 34 31 (by decide) (by decide) (by decide)
    (parsed (Computability.encodeNat a.1) (KS.W08.denseMatrixTape a.2)) rfl rfl
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [parsed,matrixState,state,Function.update]

lemma extract_spec {n : ℕ} (v : Option (Fin n → ℚ)) : RunSpec extract
    (witnessState v) (io (v.elim [] KS.W12.RowDot.vectorTape))
    (2*(v.elim [] KS.W12.RowDot.vectorTape).length+2) := by
  have h := CleanRoutine.transfer_spec (23 : Fin 35) 34 0 (by decide) (by decide) (by decide)
    (witnessState v) rfl rfl
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [witnessState,state,io,Function.update]

def controllerTicks (a : Datum) : ℕ :=
  KS.W29.polynomialFuel KS.W23.PSDControllerPolynomial.coefficient 58
    (KS.W08.denseMatrixTape a.2).length

def ticks (a : Datum) : ℕ :=
  (3*(Computability.encodeNat a.1).length+2)+(2*(KS.W08.denseMatrixTape a.2).length+2)+
    controllerTicks a+(2*(output a).length+2)

lemma program_spec (a : Datum) : RunSpec program (io (input a)) (io (output a)) (ticks a) := by
  have h := (decode_spec a).compose ((install_spec a).compose
    ((KS.W23.PSDControllerPolynomial.controller_polynomial_spec a.2).compose
      (extract_spec (rationalNegativeWitness a.1 (DenseRatMatrix.decode a.2)))))
  simp only [ticks,output,Nat.add_assoc] at h ⊢
  exact h

def routine : Routine input output ticks where
  scratch := 34
  program := program
  spec := program_spec

lemma output_length (a : Datum) : (output a).length≤controllerTicks a := by
  have h := RoutineLength.output_length
    (KS.W23.PSDControllerPolynomial.controller_polynomial_spec a.2) (23 : Fin 35)
  simp only [output,witnessState,matrixState,state,show (23 : Fin 35)≠32 by decide,
    show (23 : Fin 35)≠26 by decide,show (23 : Fin 35)≠31 by decide,
    show (23 : Fin 35)≠30 by decide,ite_false,ite_true,List.length_nil,zero_add] at h ⊢
  exact h

lemma ticks_le (a : Datum) : ticks a≤
    3*(Computability.encodeNat a.1).length+2*(KS.W08.denseMatrixTape a.2).length+
      3*controllerTicks a+6 := by
  have h := output_length a
  unfold ticks
  omega

end CurrentKS.PSDCleanRoutine

end OAI
