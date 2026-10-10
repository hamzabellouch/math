import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalTreeLaunch
import OAI.Computability.QuantumFactoring.TreePadding

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork BitArithmetic Exactness OrderTrial

lemma parallelProgram_encoded_state {α β : Type*} [Fintype α] [Fintype β] {p q : ℕ}
    (A : List (Instruction p)) (B : List (Instruction q)) (x : Basis p) (y : Basis q)
    (e : α→Basis p) (f : β→Basis q) (ψ : α→ℂ) (χ : β→ℂ)
    (hA : (programMatrix A).mulVec (basisVector x)=encodeState e ψ)
    (hB : (programMatrix B).mulVec (basisVector y)=encodeState f χ) :
    (programMatrix (parallelProgram A B)).mulVec (basisVector (Fin.append x y))=
      encodeState (fun ab : α×β=>Fin.append (e ab.1) (f ab.2)) (independentState ψ χ) := by
  rw [parallelProgram,programMatrix_append,←Matrix.mulVec_mulVec,leftProgram_basis,hA,
    encodeState_comp,encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,rightProgram_basis,hB,encodeState_comp,Function.comp_def]
  exact (encode_independent e f ψ χ).symm

namespace PhysicalTree
abbrev launchWork (n : ℕ) := (initialNet n).net.count
abbrev launchWidth (n : ℕ) := n+width n+launchWork n

def launchProgram (n : ℕ) : List (Instruction (launchWidth n)) :=
  preparedOracle (initialNet n) le_rfl ((machine n).program (steps n))
def launchEncoding (n N : ℕ) (r : NodeMachine.Trace n (steps n)) : Basis (launchWidth n) :=
  packed (launchWork n) (natBasis n N) ((machine n).encoded (initialQueue n N) (steps n) r)
def launchZero (n N : ℕ) : Basis (launchWidth n) :=
  packed (launchWork n) (natBasis n N) (fun _=>false)

lemma launchProgram_state (n N : ℕ) :
    (programMatrix (launchProgram n)).mulVec (basisVector (launchZero n N))=
      encodeState (launchEncoding n N) ((machine n).state (initialQueue n N) (steps n)) := by
  rw [launchProgram,launchZero,preparedOracle_basis,initialNet_eval,
    NodeMachine.program_state,encodeState_comp]
  rfl
lemma launchEncoding_injective (n N : ℕ) : Function.Injective (launchEncoding n N) := by
  intro a b h
  apply (machine n).encoded_injective (initialQueue n N) (steps n)
  have he:=congrArg (fun x=>x ∘ targetRegister n (width n) (launchWork n)) h
  simpa only [launchEncoding,packed_targetRegister] using he

abbrev paddedWidth (n : ℕ) := launchWidth n+tensorWidth n (padding n)
def paddedProgram (n : ℕ) : List (Instruction (paddedWidth n)) :=
  parallelProgram (launchProgram n) (padProgram n)
def paddedZero (n N : ℕ) : Basis (paddedWidth n) :=
  Fin.append (launchZero n N) (tensorLayout n (padding n) (fun _ _=>false))
def paddedEncoding (n N : ℕ) (r : PaddedRaw n) : Basis (paddedWidth n) :=
  Fin.append (launchEncoding n N r.1) (tensorLayout n (padding n) r.2)

lemma paddedProgram_state (n N : ℕ) :
    (programMatrix (paddedProgram n)).mulVec (basisVector (paddedZero n N))=
      encodeState (paddedEncoding n N) (paddedState n N) :=
  parallelProgram_encoded_state _ _ _ _ _ _ _ _ (launchProgram_state n N) (padProgram_state n)

lemma paddedEncoding_injective (n N : ℕ) : Function.Injective (paddedEncoding n N) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have he : (launchEncoding n N a,tensorLayout n (padding n) b)=
      (launchEncoding n N c,tensorLayout n (padding n) d) := (appendEquiv _ _).injective h
  have hac:=launchEncoding_injective n N (congrArg Prod.fst he)
  have hbd:=(tensorLayout n (padding n)).injective (congrArg Prod.snd he)
  cases hac
  cases hbd
  rfl

lemma launchProgram_length (n : ℕ) : (launchProgram n).length≤
    4*launchWork n+2*width n+((machine n).program (steps n)).length :=
  preparedOracle_length _ _ _
lemma paddedProgram_length (n : ℕ) : (paddedProgram n).length≤
    4*launchWork n+2*width n+((machine n).program (steps n)).length+padding n*n := by
  rw [paddedProgram,parallelProgram_length,padProgram_length]
  exact Nat.add_le_add_right (launchProgram_length n) _

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
