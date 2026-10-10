import Mathlib
import OAI.Computability.QuantumFactoring.PackedPrograms
import OAI.Computability.QuantumFactoring.RecordedHistory

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

def targetRegister (n m r : ℕ) : Register m (n+m+r) where
  toFun i := ⟨n+i.val,by omega⟩
  inj' := by
    intro i j hh
    apply Fin.ext
    have h := congrArg Fin.val hh
    change n+i.val=n+j.val at h
    omega

lemma targetRegister_val (n m r : ℕ) (i : Fin m) :
    (targetRegister n m r i).val=n+i.val := rfl

lemma packed_targetRegister {n m r : ℕ} (x : Basis n) (y : Basis m) :
    packed r x y ∘ targetRegister n m r=y := by
  funext i
  exact packed_target x y i

lemma packed_replace_target {n m r : ℕ} (x : Basis n) (y z : Basis m) :
    (targetRegister n m r).replace (packed r x y) z=packed r x z := by
  funext i
  by_cases hin : n ≤ i.val
  · by_cases hi : i.val<n+m
    · let j : Fin m := ⟨i.val-n,by omega⟩
      have he : targetRegister n m r j=i := Fin.ext (by rw [targetRegister_val]; dsimp [j]; omega)
      rw [←he,Register.replace_inside]
      exact (packed_target x z j).symm
    · have ho : ∀ j,targetRegister n m r j≠i := by
        intro j hh
        have he := congrArg Fin.val hh
        rw [targetRegister_val] at he
        have := j.isLt
        omega
      rw [Register.replace_outside _ _ _ ⟨i,ho⟩]
      change packed r x y i=packed r x z i
      rw [packed_work _ _ _ (by omega),packed_work _ _ _ (by omega)]
  · have ho : ∀ j,targetRegister n m r j≠i := by
      intro j hh
      have he := congrArg Fin.val hh
      rw [targetRegister_val] at he
      omega
    rw [Register.replace_outside _ _ _ ⟨i,ho⟩]
    simp only [packed,dite_eq_left (show i.val<n by omega)]

def targetProgram {m : ℕ} (n r : ℕ) (ops : List (Instruction m)) :
    List (Instruction (n+m+r)) := ops.map (Instruction.place (targetRegister n m r))

lemma targetProgram_basis {n m r : ℕ} (ops : List (Instruction m)) (x : Basis n) (y : Basis m) :
    (programMatrix (targetProgram n r ops)).mulVec (basisVector (packed r x y))=
      encodeState (fun z => packed r x z) ((programMatrix ops).mulVec (basisVector y)) := by
  rw [targetProgram,Register.placed_basis_state,packed_targetRegister]
  congr 1
  funext z
  exact packed_replace_target x y z

/-- Prepare a runtime-dependent input with a genuine clean Boolean oracle,
then run the same fixed quantum program on that fresh input. All old bits x
survive, and c is a network, not a large table of counterfactual outputs. -/
def preparedOracle {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction m)) : List (Instruction (n+m+r)) :=
  oracleOn c hr++targetProgram n r ops

lemma preparedOracle_length {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction m)) :
    (preparedOracle c hr ops).length ≤ 4*c.net.count+2*m+ops.length := by
  have hh := oracleOn_length c hr
  simp only [preparedOracle,List.length_append,targetProgram,List.length_map]
  omega

lemma preparedOracle_basis {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction m)) (x : Basis n) :
    (programMatrix (preparedOracle c hr ops)).mulVec (basisVector (packed r x (fun _ => false)))=
      encodeState (fun z => packed r x z) ((programMatrix ops).mulVec (basisVector (c.eval x))) := by
  rw [preparedOracle,programMatrix_append,←Matrix.mulVec_mulVec,oracleOn_basis]
  simp only [Bool.false_xor]
  exact targetProgram_basis ops x _

/-- Coherent launch on an arbitrary already-entangled classical history. This
identity is valid on the actual amplitudes, prior to any later validation. -/
lemma preparedOracle_state {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction m)) (ψ : State n) :
    (programMatrix (preparedOracle c hr ops)).mulVec
      (encodeState (fun x => packed r x (fun _ => false)) ψ)=
    encodeState (fun xy : Basis n×Basis m => packed r xy.1 xy.2)
      (RecordedHistory.appendState ψ (fun x => (programMatrix ops).mulVec (basisVector (c.eval x)))) := by
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,preparedOracle_basis]
  unfold encodeState RecordedHistory.appendState
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [smul_smul]

lemma packed_pair_injective (n m r : ℕ) :
    Function.Injective (fun xy : Basis n×Basis m => packed r xy.1 xy.2) := by
  intro x y h
  apply Prod.ext
  · have he := congrArg (fun a => a ∘ firstRegister n m r) h
    simpa only [packed_first] using he
  · have he := congrArg (fun a => a ∘ targetRegister n m r) h
    simpa only [packed_targetRegister] using he

end ExactQuantumFactoring


end

end OAI
