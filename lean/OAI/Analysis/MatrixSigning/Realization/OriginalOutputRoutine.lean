import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.Outside
import OAI.Analysis.MatrixSigning.Realization.OriginalSignRealization
import OAI.Analysis.MatrixSigning.Realization.OriginalParserRoutine

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

abbrev wordCode : Word → Word := id

def appendBit : Realizes (prodCode wordCode boolCode) wordCode (fun p => p.1++[p.2]) where
  cost := fun p => 5*p.1.length+4
  routine := WordOperations.appending.reindex (fun p : Word×Bool => (p.1,[p.2]))
lemma fold_appendBit (xs ys : Word) : xs.foldl (fun acc b => acc++[b]) ys=ys++xs := by
  induction xs generalizing ys with
  | nil => simp
  | cons b xs ih => simp only [List.foldl_cons,ih,List.append_assoc,List.singleton_append]

def outputBits : Realizes (listCode boolCode) wordCode id :=
  (((constant (listCode boolCode) wordCode []).both (identity (listCode boolCode))).then appendBit.fold).congr
    (by intro xs;simpa using fold_appendBit xs [])

def fullBody : Realizes Input.encode wordCode RationalInput.signing :=
  ({cost := OriginalParserRoutine.ticks,routine := OriginalParserRoutine.routine} :
    Realizes Input.encode originalCode id).then (originalSigningFramed.then outputBits)

end CurrentKS.Realization

namespace CurrentKS.OriginalTailRoutine
open CleanRoutine Realization
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def clearD : Program 5 := KS.W04.BinaryStackMoves.clearProgram 1
def clearN : Program 5 := KS.W04.BinaryStackMoves.clearProgram 2
def program : Program 5 := compose DenseInputMachine.readHeader (compose clearD clearN)
lemma clearD_spec (source d n : Word) : RunSpec clearD (DenseInputMachine.layout source d n [] [])
    (DenseInputMachine.layout source [] n [] []) (d.length+1) := by
  have h := KS.W15.RationalMultiply.clear_spec (1 : Fin 5) (DenseInputMachine.layout source d n [] [])
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [DenseInputMachine.layout,KS.W15.RationalMultiply.clearAfter]
lemma clearN_spec (source n : Word) : RunSpec clearN (DenseInputMachine.layout source [] n [] [])
    (io source) (n.length+1) := by
  have h := KS.W15.RationalMultiply.clear_spec (2 : Fin 5) (DenseInputMachine.layout source [] n [] [])
  convert h using 1 <;> (try rfl)
  funext j;fin_cases j <;> simp [DenseInputMachine.layout,io,KS.W15.RationalMultiply.clearAfter]
def ticks (x : Input) : ℕ := DenseInputMachine.headerTicks x.d x.N+
    ((Computability.encodeNat x.d).length+1)+((Computability.encodeNat x.N).length+1)
lemma program_spec (x : Input) : RunSpec program (io x.encode) (io (DenseInputMachine.denseTape x)) (ticks x) := by
  have h := (DenseInputMachine.readHeader_spec x []).compose
    ((clearD_spec (DenseInputMachine.denseTape x) (Computability.encodeNat x.d) (Computability.encodeNat x.N)).compose
      (clearN_spec (DenseInputMachine.denseTape x) (Computability.encodeNat x.N)))
  have he : io x.encode=DenseInputMachine.layout x.encode [] [] [] [] := by funext j;fin_cases j <;> rfl
  simp only [he,ticks,Nat.add_assoc] at h ⊢
  exact h

def routine : Routine Input.encode DenseInputMachine.denseTape ticks := ⟨4,program,program_spec⟩
lemma ticks_le (x : Input) : ticks x≤3*x.length+2 := by
  have h := DenseInputMachine.headerTicks_le x
  have hb : (Computability.encodeNat x.d).length+(Computability.encodeNat x.N).length≤x.length := by
    simp only [Input.length,Input.encode,List.length_append,CurrentKS.encodeNat,DenseInputMachine.length_frame]
    omega
  unfold ticks
  omega

end CurrentKS.OriginalTailRoutine

namespace CurrentKS.Realization
open CleanRoutine

def originalEmpty : Realizes Input.encode boolCode (fun x => decide (x.N=0)) :=
  let tail : Realizes Input.encode wordCode DenseInputMachine.denseTape :=
    ⟨OriginalTailRoutine.ticks,OriginalTailRoutine.routine⟩
  let empty : Realizes wordCode boolCode List.isEmpty :=
    ⟨fun w => w.length+6,WordOperations.isEmpty⟩
  (tail.then empty).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [List.isEmpty_iff,decide_eq_true_eq]
    exact DenseInputMachine.denseTape_eq_nil_iff x)

lemma signing_empty (x : Input) (h : x.N=0) : RationalInput.signing x=[] := by
  have he : RationalInput.indices x=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i hi
    exact (Nat.not_lt_zero i.val) (h ▸ i.isLt)
  simp [RationalInput.signing,he,h]

def originalSigning : Realizes Input.encode wordCode RationalInput.signing :=
  (originalEmpty.ite (constant Input.encode wordCode []) fullBody).congr (by
    intro x
    by_cases h : x.N=0
    · simp [h,signing_empty x h]
    · simp [h])

theorem originalSigning_good (x : Input) (hx : Admissible x) :
    GoodOutput x (RationalInput.signing x) := RationalInput.signing_good x hx

end CurrentKS.Realization

end OAI
