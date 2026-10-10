import OAI.Computability.PerfectCompleteness.Foundations.CanonicalDictionaryNames
import OAI.Computability.PerfectCompleteness.Machines.CanonicalKeyMachine
import OAI.Computability.UniqueGames.Machines.MachineDrain

namespace OAI


namespace PerfectCompleteness.CanonicalEndpointMachine


open Turing UniqueGamesTheorem.Foundations.Complexity MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer
open CanonicalKeys CanonicalKeyShape ClauseSupport
open scoped Classical

noncomputable section

variable {n : Nat} {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := CanonicalDictionaryMachine.State A
abbrev clean (ambient : A) : State A := CanonicalDictionaryMachine.clean ambient

inductive Label (n : Nat)
  | key (label : CanonicalKeyMachine.Label n)
  | reverse
  | dictionary (label : CanonicalDictionaryMachine.Label)
  | drainKey
  deriving DecidableEq, Fintype

def main (n : Nat) : Label n := .key (.inl ())

def instruction (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue)))
    (tape : Fin n → Fin 6 → K) (forwardKey : K) (dictionary : Fin 8 → K)
    (labels : Label n → Λ) (done rejected : Option Λ) :
    Label n → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .key label => CanonicalKeyMachine.instruction shapes modes side partition tape forwardKey
      (fun l => labels (.key l)) (some (labels .reverse)) label
  | .reverse => loopAt forwardKey (dictionary 0) id false (labels .reverse)
      (some (labels (.dictionary CanonicalDictionaryMachine.main)))
  | .dictionary label => CanonicalDictionaryMachine.instruction dictionary
      (fun l => labels (.dictionary l)) (some (labels .drainKey)) rejected label
  | .drainKey => MachineDrain.drain (dictionary 0) (labels .drainKey) done

def finalTapes (dictionary : Fin 8 → K) (base : K → List Bool)
    (earlier : List (Key n)) (key : Key n) : K → List Bool :=
  Function.update (Function.update base (dictionary 1)
    (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key])))) (dictionary 7)
      ((encodeWord (CanonicalOnlineNames.onlineID earlier key)).reverse ++ base (dictionary 7))

def budget (tape : Fin n → Fin 6 → K) (base : K → List Bool)
    (earlier : List (Key n)) (key : Key n) : Nat :=
  ((2 * CanonicalKeyMachine.sourceLength tape base + 4 * n + 2) +
      ((CanonicalVertexNames.payload key).length + 1)) +
    (3 * (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length ^ 2 +
      16 * (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length + 12) +
    ((CanonicalVertexNames.payload key).length + 1)

def endpointInTime (shapes : Fin n → Shape) (modes : Fin n → SupportMode) (side : Side)
    (partition : Set (Set (Fin n → ReducedValue)))
    (occurrences : Fin n → Nat) (variableIDs : Fin n → Fin 3 → Nat)
    (tape : Fin n → Fin 6 → K) (distinct : ∀ i, Function.Injective (tape i))
    (forwardKey : K) (dictionary : Fin 8 → K)
    (dictionaryDistinct : Function.Injective dictionary)
    (forwardDistinct : ∀ i, forwardKey ≠ dictionary i)
    (sharedScratch : ∀ i, tape i 4 = dictionary 5)
    (sharedOutput : ∀ i, tape i 5 = forwardKey)
    (labels : Label n → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) =
      instruction shapes modes side partition tape forwardKey dictionary labels done rejected l)
    (base : K → List Bool) (ambient : A) (earlier : List (Key n))
    (sourceWords : ∀ i field, base (KeyMetadataMachine.idTape (tape i) field) =
      encodeWord (KeyMetadataMachine.fieldValue (occurrences i) (variableIDs i) field))
    (forwardEmpty : base forwardKey = []) (keyEmpty : base (dictionary 0) = [])
    (dictionaryWord : base (dictionary 1) =
      BinaryNameSearch.stream (CanonicalVertexNames.tokens earlier))
    (empty : ∀ i : Fin 8, 2 ≤ i.val → i.val ≤ 6 → base (dictionary i) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (main n)), clean ambient, base⟩
      (some ⟨done, clean ambient, finalTapes dictionary base earlier
        (CanonicalKeyMachine.recoveredKey shapes modes side partition occurrences variableIDs)⟩)
      (budget tape base earlier
        (CanonicalKeyMachine.recoveredKey shapes modes side partition occurrences variableIDs)) := by
  let key := CanonicalKeyMachine.recoveredKey shapes modes side partition occurrences variableIDs
  let bits := CanonicalVertexNames.payload key
  let s₁ := Function.update base forwardKey bits
  let s₂ := Function.update base (dictionary 0) bits.reverse
  let s₃ := Function.update (Function.update s₂ (dictionary 1)
    (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key])))) (dictionary 7)
      ((encodeWord (CanonicalOnlineNames.onlineID earlier key)).reverse ++ base (dictionary 7))
  have hd (i j : Fin 8) (hne : i ≠ j) : dictionary i ≠ dictionary j :=
    fun h => hne (dictionaryDistinct h)
  have payloadEq : CanonicalKeyMachine.payload shapes modes side partition occurrences variableIDs =
      bits := rfl
  have keyEntry : CanonicalKeyMachine.entry (fun l => labels (.key l))
      (some (labels .reverse)) = some (labels (main n)) := rfl
  have produced : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (main n)), clean ambient, base⟩
      (some ⟨some (labels .reverse), clean ambient, s₁⟩)
      (2 * CanonicalKeyMachine.sourceLength tape base + 4 * n + 2) := by
    have run := CanonicalKeyMachine.keyInTime shapes modes side partition occurrences variableIDs
      tape distinct (dictionary 5) forwardKey (Ne.symm (forwardDistinct 5))
      sharedScratch sharedOutput (fun l => labels (.key l)) (some (labels .reverse))
      program (fun l => atLabels (.key l)) base sourceWords
      (empty 5 (by decide) (by decide)) (ambient, false, none)
    simpa only [keyEntry, payloadEq, forwardEmpty, List.append_nil, s₁,
      KeyMetadataMachine.clean, clean, CanonicalDictionaryMachine.clean, BinaryNameCompare.clean]
      using run
  have s₁forward : s₁ forwardKey = bits := by simp [s₁]
  have s₁key : s₁ (dictionary 0) = [] := by
    simp [s₁, Ne.symm (forwardDistinct 0), keyEmpty]
  have transferredTapes : tapesAt forwardKey (dictionary 0) s₁ [] bits.reverse = s₂ := by
    funext k
    by_cases h0 : k = dictionary 0
    · subst k
      simp [tapesAt, s₁, s₂]
    · by_cases hf : k = forwardKey
      · subst k
        simp [tapesAt, s₁, s₂, forwardDistinct 0, forwardEmpty]
      · simp [tapesAt, s₁, s₂, h0, hf]
  have transferred : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .reverse), clean ambient, s₁⟩
      (some ⟨some (labels (.dictionary CanonicalDictionaryMachine.main)), clean ambient, s₂⟩)
      (bits.length + 1) := by
    have run := transferAtInTime (Γ := Alphabet) forwardKey (dictionary 0)
      (forwardDistinct 0) id false (labels .reverse)
      (some (labels (.dictionary CanonicalDictionaryMachine.main))) program (atLabels .reverse)
      s₁ (ambient, false, none) none
    simpa only [s₁forward, s₁key, List.map_id_fun, id_eq, List.append_nil, transferredTapes,
      clean, CanonicalDictionaryMachine.clean, BinaryNameCompare.clean] using run
  have s₂key : s₂ (dictionary 0) = bits.reverse := by simp [s₂]
  have s₂dictionary : s₂ (dictionary 1) =
      BinaryNameSearch.stream (CanonicalVertexNames.tokens earlier) := by
    simp [s₂, hd 1 0 (by decide), dictionaryWord]
  have s₂accumulator : s₂ (dictionary 7) = base (dictionary 7) := by
    simp [s₂, hd 7 0 (by decide)]
  have s₂empty (i : Fin 8) (lo : 2 ≤ i.val) (hi : i.val ≤ 6) : s₂ (dictionary i) = [] := by
    have ne : i ≠ 0 := by intro h; subst i; omega
    simp [s₂, hd i 0 ne, empty i lo hi]
  have named : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.dictionary CanonicalDictionaryMachine.main)), clean ambient, s₂⟩
      (some ⟨some (labels .drainKey), clean ambient, s₃⟩)
      (3 * (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length ^ 2 +
        16 * (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length + 12) := by
    have run := CanonicalDictionaryNames.dictionaryInTime dictionary dictionaryDistinct
      (fun l => labels (.dictionary l)) (some (labels .drainKey)) rejected program
      (fun l => atLabels (.dictionary l)) s₂ ambient earlier key s₂key s₂dictionary s₂empty
    simpa only [s₂accumulator, s₃, clean] using run
  have s₃key : s₃ (dictionary 0) = bits.reverse := by
    simp [s₃, s₂, hd 0 7 (by decide), hd 0 1 (by decide)]
  have restored : Function.update s₃ (dictionary 0) [] = finalTapes dictionary base earlier key := by
    funext k
    by_cases h0 : k = dictionary 0
    · subst k
      simp [finalTapes, hd 0 7 (by decide), hd 0 1 (by decide), keyEmpty]
    · simp [s₃, s₂, finalTapes, Function.update_apply, h0]
  have drained : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .drainKey), clean ambient, s₃⟩
      (some ⟨done, clean ambient, finalTapes dictionary base earlier key⟩)
      (bits.length + 1) := by
    have run := MachineDrain.drainInTime (dictionary 0) (labels .drainKey) done program
      (atLabels .drainKey) s₃ (ambient, false, none) none
    simpa only [s₃key, List.length_reverse, restored, clean,
      CanonicalDictionaryMachine.clean, BinaryNameCompare.clean] using run
  have first := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ produced transferred
  have second := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ first named
  have all := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ second drained
  simpa only [budget, bits, key, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

theorem finalTapes_frame (dictionary : Fin 8 → K) (base : K → List Bool)
    (earlier : List (Key n)) (key : Key n) (k : K)
    (notDictionary : k ≠ dictionary 1) (notAccumulator : k ≠ dictionary 7) :
    finalTapes dictionary base earlier key k = base k := by
  simp only [finalTapes, Function.update_of_ne notAccumulator,
    Function.update_of_ne notDictionary]

theorem finalTapes_sources (tape : Fin n → Fin 6 → K) (dictionary : Fin 8 → K)
    (base : K → List Bool) (earlier : List (Key n)) (key : Key n)
    (notDictionary : ∀ i field, KeyMetadataMachine.idTape (tape i) field ≠ dictionary 1)
    (notAccumulator : ∀ i field, KeyMetadataMachine.idTape (tape i) field ≠ dictionary 7)
    (i : Fin n) (field : Fin 4) :
    finalTapes dictionary base earlier key (KeyMetadataMachine.idTape (tape i) field) =
      base (KeyMetadataMachine.idTape (tape i) field) :=
  finalTapes_frame dictionary base earlier key _ (notDictionary i field) (notAccumulator i field)

theorem label_finite : Finite (Label n) := inferInstance

theorem state_finite [Finite A] : Finite (State A) := inferInstance

omit [DecidableEq K] in
theorem workAlphabet_finite (k : K) : Finite (Alphabet k) := inferInstance

end

end PerfectCompleteness.CanonicalEndpointMachine

end OAI
