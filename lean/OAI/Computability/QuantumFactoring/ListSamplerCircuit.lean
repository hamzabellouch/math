import Mathlib
import OAI.Computability.QuantumFactoring.FairOracle
import OAI.Computability.QuantumFactoring.RuntimeListPreparation

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.ListSampler
open Exactness BitArithmetic BooleanNetwork

abbrev work (n : ℕ) := n*(49*n+8)
abbrev width (n : ℕ) := n+n+(n+work n)

def word {n : ℕ} (m mask y : Basis n) : Basis (width n) := fun i =>
  if h₀ : i.val<n then m ⟨i.val,h₀⟩ else
  if h₁ : i.val<n+n then mask ⟨i.val-n,by omega⟩ else
  if h₂ : i.val<n+n+n then y ⟨i.val-(n+n),by omega⟩ else false

lemma word_input {n : ℕ} (m mask y : Basis n) (i : Fin n) :
    word m mask y ⟨i.val,by have := i.isLt; dsimp [width]; omega⟩=m i := by
  simp only [word,i.isLt,dite_eq_left]

lemma word_mask {n : ℕ} (m mask y : Basis n) (i : Fin n) :
    word m mask y ⟨n+i.val,by have := i.isLt; dsimp [width]; omega⟩=mask i := by
  have h₀ : ¬n+i.val<n := by omega
  have h₁ : n+i.val<n+n := by omega
  simp only [word,dite_eq_right h₀,dite_eq_left h₁,Nat.add_sub_cancel_left]

lemma word_sample {n : ℕ} (m mask y : Basis n) (i : Fin n) :
    word m mask y ⟨n+n+i.val,by have := i.isLt; dsimp [width]; omega⟩=y i := by
  have h₀ : ¬n+n+i.val<n := by omega
  have h₁ : ¬n+n+i.val<n+n := by omega
  have h₂ : n+n+i.val<n+n+n := by omega
  simp only [word,dite_eq_right h₀,dite_eq_right h₁,dite_eq_left h₂,Nat.add_sub_cancel_left]

lemma word_work {n : ℕ} (m mask y : Basis n) (i : Fin (width n)) (hi : n+n+n ≤ i.val) :
    word m mask y i=false := by
  simp only [word,dite_eq_right (show ¬i.val<n by omega),dite_eq_right (show ¬i.val<n+n by omega),
    dite_eq_right (Nat.not_lt.mpr hi)]

lemma packed_word {n : ℕ} (m mask : Basis n) :
    packed (n+work n) m mask=word m mask (fun _ => false) := by
  funext i
  unfold packed word
  split_ifs <;> rfl

def maskRegister (n : ℕ) : Register (n+n) (width n) where
  toFun i := ⟨n+i.val,by have := i.isLt; dsimp [width]; omega⟩
  inj' := by
    intro i j hh
    apply Fin.ext
    have h := congrArg Fin.val hh
    dsimp at h
    omega

lemma maskRegister_val (n : ℕ) (i : Fin (n+n)) : (maskRegister n i).val=n+i.val := rfl

lemma word_register {n : ℕ} (m mask y : Basis n) :
    word m mask y ∘ maskRegister n=Fin.append mask y := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact (word_mask m mask y j).trans (Fin.append_left _ _ _).symm
  · have he : maskRegister n (Fin.natAdd n j)=⟨n+n+j.val,by have := j.isLt; dsimp [width]; omega⟩ :=
      Fin.ext (by simp only [maskRegister_val,Fin.val_natAdd]; omega)
    rw [Function.comp_apply,he,word_sample,Fin.append_right]

lemma word_replace {n : ℕ} (m mask y mask' y' : Basis n) :
    (maskRegister n).replace (word m mask y) (Fin.append mask' y')=word m mask' y' := by
  funext i
  by_cases hi₀ : i.val<n
  · have ho : ∀ j,maskRegister n j≠i := by
      intro j hh
      have h := congrArg Fin.val hh
      rw [maskRegister_val] at h
      omega
    rw [Register.replace_outside _ _ _ ⟨i,ho⟩]
    simp only [word,hi₀,dite_eq_left]
  · by_cases hi₁ : i.val<n+n+n
    · let j : Fin (n+n) := ⟨i.val-n,by omega⟩
      have he : maskRegister n j=i := Fin.ext (by rw [maskRegister_val]; dsimp [j]; omega)
      rw [←he,Register.replace_inside]
      exact (congrFun (word_register m mask' y') j).symm
    · have ho : ∀ j,maskRegister n j≠i := by
        intro j hh
        have h := congrArg Fin.val hh
        rw [maskRegister_val] at h
        have := j.isLt
        omega
      rw [Register.replace_outside _ _ _ ⟨i,ho⟩]
      change word m mask y i=word m mask' y' i
      rw [word_work _ _ _ _ (by omega),word_work _ _ _ _ (by omega)]

/-- A single family (depending only on n) prepares the manuscript's exact
runtime-b(n,m) fair sample. No Hadamard is chosen by a metalevel value of m. -/
def circuit (n : ℕ) : List (Instruction (width n)) :=
  oracleOn (listMaskNet n) (show (listMaskNet n).net.count ≤ n+work n from
    (listMaskNet_count n).trans (Nat.le_add_left _ _)) ++
  (maskedPrefix n n le_rfl).map (Instruction.place (maskRegister n))

lemma circuit_length (n : ℕ) : (circuit n).length ≤ 4*work n+3*n := by
  have h := oracleOn_length (listMaskNet n) (show (listMaskNet n).net.count ≤ n+work n from
    (listMaskNet_count n).trans (Nat.le_add_left _ _))
  have hc : (listMaskNet n).net.count ≤ work n := listMaskNet_count n
  simp only [circuit,List.length_append,List.length_map,maskedPrefix_length]
  omega

lemma circuit_state (n : ℕ) (m : Basis n) :
    (programMatrix (circuit n)).mulVec
      (basisVector (word m (fun _ => false) (fun _ => false)))=
    encodeState (fun y => word m ((listMaskNet n).eval m)
      (padBits (Nat.clog_le_of_le_pow (bitsValue m).isLt.le) y))
      (fairState (Nat.clog 2 (bitsValue m).toNat)) := by
  rw [circuit,programMatrix_append,←Matrix.mulVec_mulVec,←packed_word,
    oracleOn_basis]
  simp only [Bool.false_xor]
  rw [packed_word,Register.placed_basis_state,word_register,maskedList_state,
    encodeState_comp]
  congr 1
  funext y
  exact word_replace _ _ _ _ _

lemma word_injective {n : ℕ} (m mask : Basis n) : Function.Injective (word m mask) := by
  intro x y h
  funext i
  have he := congrFun h ⟨n+n+i.val,by have := i.isLt; dsimp [width]; omega⟩
  simpa only [word_sample] using he

/-- Born events in the actual prepared register are exactly the b(n,m)-bit
fair events, retaining the original input, mask and all clean work wires. -/
lemma circuit_mass (n : ℕ) (m : Basis n) (P : Basis (width n)→Prop) :
    outcomeMass P ((programMatrix (circuit n)).mulVec
      (basisVector (word m (fun _ => false) (fun _ => false))))=
    outcomeMass (fun y => P (word m ((listMaskNet n).eval m)
      (padBits (Nat.clog_le_of_le_pow (bitsValue m).isLt.le) y)))
      (fairState (Nat.clog 2 (bitsValue m).toNat)) := by
  rw [circuit_state]
  exact outcomeMass_encode _ ((word_injective _ _).comp (padBits_injective _)) _ _

end ExactQuantumFactoring.ListSampler


end

end OAI
