import OAI.Computability.PerfectCompleteness.Machines.CanonicalDictionaryMachine
import OAI.Computability.PerfectCompleteness.Machines.CanonicalKeyShapeMachineLemmas

namespace OAI


namespace PerfectCompleteness.CanonicalDictionaryNames

open CanonicalKeys Turing
open UniqueGamesTheorem.Foundations.Complexity MachineComposition

noncomputable section

variable {n : Nat}

theorem updatedTokens_eq (earlier : List (Key n)) (key : Key n) :
    CanonicalDictionaryMachine.updatedTokens (CanonicalVertexNames.tokens earlier)
      (CanonicalVertexNames.payload key) =
        CanonicalVertexNames.tokens (earlier ++ [key]) :=
  (CanonicalOnlineNames.tokens_append_current earlier key).symm

theorem keyWord_eq (key : Key n) :
    (CanonicalVertexNames.payload key).reverse =
      (CanonicalKeyEncoding.bits key ++ [true]).reverse := rfl

theorem index_eq_onlineID (earlier : List (Key n)) (key : Key n) :
    CanonicalDictionaryMachine.index (CanonicalVertexNames.tokens earlier)
      (CanonicalVertexNames.payload key) = CanonicalOnlineNames.onlineID earlier key := by
  unfold CanonicalDictionaryMachine.index CanonicalOnlineNames.onlineID
  rw [updatedTokens_eq]

theorem index_eq_finalName (earlier suffix : List (Key n)) (key : Key n) :
    CanonicalDictionaryMachine.index (CanonicalVertexNames.tokens earlier)
      (CanonicalVertexNames.payload key) =
        (CanonicalVertexNames.name (earlier ++ key :: suffix) key (by simp)).val := by
  rw [index_eq_onlineID, CanonicalOnlineNames.onlineID_eq_name_val earlier suffix key]

def steps (earlier : List (Key n)) (key : Key n) : Nat :=
  CanonicalDictionaryMachine.steps (CanonicalVertexNames.tokens earlier)
    (CanonicalVertexNames.payload key)

theorem steps_le (earlier : List (Key n)) (key : Key n) :
    steps earlier key ≤
      3 * (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length ^ 2 +
      16 * (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length +
      12 := by
  simpa only [steps, updatedTokens_eq] using
    CanonicalDictionaryMachine.steps_le (CanonicalVertexNames.tokens earlier)
      (CanonicalVertexNames.payload key)

def streamBound (n bound count : Nat) : Nat :=
  (2 * CanonicalVertexNames.payloadBound n bound + 2) * count

theorem steps_le_metadata (earlier : List (Key n)) (key : Key n) (bound : Nat)
    (hretained : ∀ k ∈ earlier ++ [key], k.retained.length ≤ n)
    (hIDs : ∀ k ∈ earlier ++ [key], ∀ entry ∈ k.retained,
      KeyMetadataEncoding.entryID entry.2 ≤ bound) :
    steps earlier key ≤
      3 * streamBound n bound (earlier.length + 1) ^ 2 +
      16 * streamBound n bound (earlier.length + 1) + 12 := by
  have hstream :
      (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length ≤
        streamBound n bound (earlier.length + 1) := by
    simpa only [streamBound, List.length_append, List.length_singleton] using
      CanonicalVertexNames.stream_length_le (earlier ++ [key]) bound hretained hIDs
  have hsquare := Nat.mul_le_mul hstream hstream
  apply (steps_le earlier key).trans
  nlinarith


variable {K Λ A : Type} [DecidableEq K]

theorem dictionaryTrace (tape : Fin 8 → K) (distinct : Function.Injective tape)
    (labels : CanonicalDictionaryMachine.Label → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (CanonicalDictionaryMachine.Alphabet (K := K)) Λ
      (CanonicalDictionaryMachine.State A))
    (atLabels : ∀ l, program (labels l) =
      CanonicalDictionaryMachine.instruction tape labels done rejected l)
    (base : K → List Bool) (ambient : A) (earlier : List (Key n)) (key : Key n)
    (keyWord : base (tape 0) = (CanonicalVertexNames.payload key).reverse)
    (dictionaryWord : base (tape 1) =
      BinaryNameSearch.stream (CanonicalVertexNames.tokens earlier))
    (empty : ∀ i : Fin 8, 2 ≤ i.val → i.val ≤ 6 → base (tape i) = []) :
    (advance (TM2.step program))^[steps earlier key]
      (some ⟨some (labels CanonicalDictionaryMachine.main),
        CanonicalDictionaryMachine.clean ambient, base⟩) =
      some ⟨done, CanonicalDictionaryMachine.clean ambient,
        Function.update (Function.update base (tape 1)
          (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key])))) (tape 7)
          ((encodeWord (CanonicalOnlineNames.onlineID earlier key)).reverse ++ base (tape 7))⟩ := by
  simpa only [steps, updatedTokens_eq, index_eq_onlineID] using
    CanonicalDictionaryMachine.dictionaryTrace tape distinct labels done rejected program
      atLabels base ambient (CanonicalVertexNames.tokens earlier) (CanonicalVertexNames.payload key)
      (CanonicalVertexNames.payload_canonical key) (CanonicalVertexNames.tokens_canonical earlier)
      keyWord dictionaryWord empty

def dictionaryInTime (tape : Fin 8 → K) (distinct : Function.Injective tape)
    (labels : CanonicalDictionaryMachine.Label → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (CanonicalDictionaryMachine.Alphabet (K := K)) Λ
      (CanonicalDictionaryMachine.State A))
    (atLabels : ∀ l, program (labels l) =
      CanonicalDictionaryMachine.instruction tape labels done rejected l)
    (base : K → List Bool) (ambient : A) (earlier : List (Key n)) (key : Key n)
    (keyWord : base (tape 0) = (CanonicalVertexNames.payload key).reverse)
    (dictionaryWord : base (tape 1) =
      BinaryNameSearch.stream (CanonicalVertexNames.tokens earlier))
    (empty : ∀ i : Fin 8, 2 ≤ i.val → i.val ≤ 6 → base (tape i) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels CanonicalDictionaryMachine.main), CanonicalDictionaryMachine.clean ambient,
        base⟩
      (some ⟨done, CanonicalDictionaryMachine.clean ambient,
        Function.update (Function.update base (tape 1)
          (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key])))) (tape 7)
          ((encodeWord (CanonicalOnlineNames.onlineID earlier key)).reverse ++ base (tape 7))⟩)
      (3 * (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length ^ 2 +
        16 * (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key]))).length +
        12) where
  steps := steps earlier key
  evals_in_steps := dictionaryTrace tape distinct labels done rejected program atLabels
    base ambient earlier key keyWord dictionaryWord empty
  steps_le_m := steps_le earlier key

theorem dictionaryTrace_finalName (tape : Fin 8 → K) (distinct : Function.Injective tape)
    (labels : CanonicalDictionaryMachine.Label → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (CanonicalDictionaryMachine.Alphabet (K := K)) Λ
      (CanonicalDictionaryMachine.State A))
    (atLabels : ∀ l, program (labels l) =
      CanonicalDictionaryMachine.instruction tape labels done rejected l)
    (base : K → List Bool) (ambient : A) (earlier suffix : List (Key n)) (key : Key n)
    (keyWord : base (tape 0) = (CanonicalVertexNames.payload key).reverse)
    (dictionaryWord : base (tape 1) =
      BinaryNameSearch.stream (CanonicalVertexNames.tokens earlier))
    (empty : ∀ i : Fin 8, 2 ≤ i.val → i.val ≤ 6 → base (tape i) = []) :
    (advance (TM2.step program))^[steps earlier key]
      (some ⟨some (labels CanonicalDictionaryMachine.main),
        CanonicalDictionaryMachine.clean ambient, base⟩) =
      some ⟨done, CanonicalDictionaryMachine.clean ambient,
        Function.update (Function.update base (tape 1)
          (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key])))) (tape 7)
          ((encodeWord (CanonicalVertexNames.name
            (earlier ++ key :: suffix) key (by simp)).val).reverse ++ base (tape 7))⟩ := by
  simpa only [CanonicalOnlineNames.onlineID_eq_name_val earlier suffix key] using
    dictionaryTrace tape distinct labels done rejected program atLabels
      base ambient earlier key keyWord dictionaryWord empty

def dictionaryInTime_metadata (tape : Fin 8 → K) (distinct : Function.Injective tape)
    (labels : CanonicalDictionaryMachine.Label → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (CanonicalDictionaryMachine.Alphabet (K := K)) Λ
      (CanonicalDictionaryMachine.State A))
    (atLabels : ∀ l, program (labels l) =
      CanonicalDictionaryMachine.instruction tape labels done rejected l)
    (base : K → List Bool) (ambient : A) (earlier : List (Key n)) (key : Key n)
    (keyWord : base (tape 0) = (CanonicalVertexNames.payload key).reverse)
    (dictionaryWord : base (tape 1) =
      BinaryNameSearch.stream (CanonicalVertexNames.tokens earlier))
    (empty : ∀ i : Fin 8, 2 ≤ i.val → i.val ≤ 6 → base (tape i) = [])
    (bound : Nat)
    (hretained : ∀ k ∈ earlier ++ [key], k.retained.length ≤ n)
    (hIDs : ∀ k ∈ earlier ++ [key], ∀ entry ∈ k.retained,
      KeyMetadataEncoding.entryID entry.2 ≤ bound) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels CanonicalDictionaryMachine.main), CanonicalDictionaryMachine.clean ambient,
        base⟩
      (some ⟨done, CanonicalDictionaryMachine.clean ambient,
        Function.update (Function.update base (tape 1)
          (BinaryNameSearch.stream (CanonicalVertexNames.tokens (earlier ++ [key])))) (tape 7)
          ((encodeWord (CanonicalOnlineNames.onlineID earlier key)).reverse ++ base (tape 7))⟩)
      (3 * streamBound n bound (earlier.length + 1) ^ 2 +
        16 * streamBound n bound (earlier.length + 1) + 12) where
  steps := steps earlier key
  evals_in_steps := dictionaryTrace tape distinct labels done rejected program atLabels
    base ambient earlier key keyWord dictionaryWord empty
  steps_le_m := steps_le_metadata earlier key bound hretained hIDs

end
end PerfectCompleteness.CanonicalDictionaryNames

end OAI
