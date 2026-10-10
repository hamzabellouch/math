import Mathlib
import OAI.Computability.QuantumFactoring.RetrospectiveTree

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials
namespace PhysicalTree

/-- The actual tree has 2n² nodes, 2n split clocks per node, one list slot and
n^5 padded base/order slots per split. This is not the n^10 padding cap. -/
def slots (n : ℕ) : ℕ := ((n^5+1)*(2*n))*(2*n^2)
def padding (n : ℕ) : ℕ := n^10-slots n

lemma slots_le {n : ℕ} (hn : 128≤n) : slots n≤n^10 := by
  have hp : 1≤n^5 := Nat.one_le_pow _ _ (by omega)
  have h₂ : 8≤n^2 := by nlinarith
  calc
    slots n ≤ ((2*n^5)*(2*n))*(2*n^2) := by
      unfold slots
      gcongr
      omega
    _ = 8*n^8 := by ring
    _ ≤ n^2*n^8 := Nat.mul_le_mul_right _ h₂
    _ = n^10 := by ring

lemma slots_add_padding {n : ℕ} (hn : 128≤n) : slots n+padding n=n^10 :=
  Nat.add_sub_of_le (slots_le hn)

abbrev PadRaw (n : ℕ) := Fin (padding n)→Basis n
noncomputable def padState (n : ℕ) : PadRaw n→ℂ := tensorState (fairState n) (padding n)
def padPassed {n : ℕ} (x : PadRaw n) : Prop := ∀ i, ¬ Completion.rare (x i)

def padProgram (n : ℕ) : List (Instruction (tensorWidth n (padding n))) :=
  tensorProgram (hadamardPrefix n n le_rfl) (padding n)

lemma padProgram_length (n : ℕ) : (padProgram n).length=padding n*n := by
  rw [padProgram,tensorProgram_length,hadamardPrefix_length]

lemma padProgram_state (n : ℕ) :
    (programMatrix (padProgram n)).mulVec
      (basisVector (tensorLayout n (padding n) (fun _ _=>false)))=
    encodeState (tensorLayout n (padding n)) (padState n) := by
  rw [padProgram,tensorProgram_state,hadamards_zero]
  rfl

lemma pad_normalized (n : ℕ) : ∑ x,Complex.normSq (padState n x)=1 :=
  tensor_normalized _ _ (fairState_normalized n)

lemma pad_mass (n : ℕ) : outcomeMass (padPassed (n:=n)) (padState n)=
    (Completion.target n:ℝ)^(padding n) := by
  change outcomeMass (fun x : PadRaw n=>∀ i,¬Completion.rare (x i))
    (tensorState (fairState n) (padding n))=_
  rw [tensor_all_mass (fairState n) (padding n) (fun y=>¬Completion.rare y),mass_compl _ _ (fairState_normalized n)]
  have hr : outcomeMass (fun x : Basis n=>Completion.rare x) (fairState n)=
      1/(2:ℝ)^n := by
    exact fair_value_mass (by positivity)
  rw [hr]
  simp only [Completion.target,Rat.cast_sub,Rat.cast_one,Rat.cast_div,
    Rat.cast_pow,Rat.cast_ofNat]

abbrev PaddedRaw (n : ℕ) := NodeMachine.Trace n (2*n^2)×PadRaw n
noncomputable def paddedState (n N : ℕ) : PaddedRaw n→ℂ :=
  independentState ((machine n).state (initialQueue n N) (2*n^2)) (padState n)
noncomputable def paddedAccepted {n N : ℕ} (hn : 0<n) (x : PaddedRaw n) : Prop :=
  accepted (N:=N) hn x.1 ∧ padPassed x.2

lemma padded_normalized (n N : ℕ) : ∑ x,Complex.normSq (paddedState n N x)=1 :=
by
  change ∑ x : NodeMachine.Trace n (2*n^2)×PadRaw n,
    Complex.normSq (independentState ((machine n).state (initialQueue n N) (2*n^2))
      (padState n) x)=1
  simp only [independentState,Complex.normSq_mul,Fintype.sum_prod_type]
  simp_rw [←Finset.mul_sum,pad_normalized,mul_one]
  exact (machine n).state_normalized _ _

/-- Exact manuscript P_n, now for the actual chronological physical tree,
retrospective checks on its own data log, and literal nonzero-word padding. -/
theorem padded_mass {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (paddedAccepted (n:=n) (N:=N) (by omega)) (paddedState n N)=
      (knownProbability n:ℝ) := by
  change outcomeMass (fun x : PaddedRaw n => accepted (N:=N) (by omega) x.1 ∧
    padPassed x.2) (independentState ((machine n).state (initialQueue n N) (2*n^2))
      (padState n))=_
  rw [independent_mass,accepted_mass hn hN hb,pad_mass,
    ←pow_mul,←pow_mul,←pow_add]
  have he : (n^5+1)*(2*n*(2*n^2))+padding n=n^10 := by
    simpa only [slots,Nat.mul_assoc] using slots_add_padding hn
  rw [he]
  simp only [knownProbability,Completion.target,Rat.cast_pow,Rat.cast_sub,
    Rat.cast_one,Rat.cast_div,Rat.cast_ofNat]

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
