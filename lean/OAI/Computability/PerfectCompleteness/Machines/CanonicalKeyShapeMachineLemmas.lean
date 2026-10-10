import Mathlib.Data.List.Basic
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalEdgesLemmas
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalVertexNames
import OAI.Computability.PerfectCompleteness.Machines.FiniteBlockMachineLemmas

namespace OAI


namespace PerfectCompleteness.CanonicalKeyShapeMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open CanonicalKeyShape CanonicalKeyEncoding CanonicalKeys

noncomputable section

def inputEnum (n k : Nat) : Input n k ≃ Fin (Fintype.card (Input n k)) :=
  Fintype.equivFin _

def inputBits {n k : Nat} (data : Input n k) : List Bool :=
  FiniteBlockMachine.word (inputEnum n k) data

def defaultInput (n : Nat) {k : Nat} (hk : 0 < k) : Input n k :=
  ⟨fun _ => Shape.bit, fun _ => ⟨0, hk⟩⟩

def modeEnum : SupportMode ≃ Fin (Fintype.card SupportMode) := Fintype.equivFin _

def modeWords {n : Nat} (support : Fin n → SupportMode) : List Nat :=
  List.ofFn (fun i => (modeEnum (support i)).val)

@[simp] theorem modeWords_length {n : Nat} (support : Fin n → SupportMode) :
    (modeWords support).length = n := List.length_ofFn

theorem modeWords_injective (n : Nat) : Function.Injective (modeWords (n := n)) := by
  intro a b h
  have hfun := List.ofFn_injective h
  funext i
  apply modeEnum.injective
  exact Fin.ext (congrFun hfun i)

def outputWords {n k : Nat} (data : Input n k) : List Nat :=
  modeWords (inputModes data) ++ partitionWords (inputPartition data)

def outputBits {n k : Nat} (data : Input n k) : List Bool := encodeWords (outputWords data)

@[simp] theorem outputWords_length {n k : Nat} (data : Input n k) :
    (outputWords data).length = n + partitionWidth n := by
  simp only [outputWords, List.length_append, modeWords_length, partitionWords_length]

theorem outputWords_eq_iff {n k : Nat} (a b : Input n k) :
    outputWords a = outputWords b ↔
      inputModes a = inputModes b ∧ inputPartition a = inputPartition b := by
  constructor
  · intro h
    have hlen : (modeWords (inputModes a)).length = (modeWords (inputModes b)).length := by
      simp only [modeWords_length]
    have hp := List.append_inj h hlen
    exact ⟨modeWords_injective n hp.1, partitionWords_injective n hp.2⟩
  · rintro ⟨hm, hp⟩
    simp only [outputWords, hm, hp]

theorem outputBits_eq_iff {n k : Nat} (a b : Input n k) :
    outputBits a = outputBits b ↔
      inputModes a = inputModes b ∧ inputPartition a = inputPartition b := by
  constructor
  · intro h
    exact (outputWords_eq_iff a b).mp (encodeWords_injective h)
  · intro h
    exact congrArg encodeWords ((outputWords_eq_iff a b).mpr h)

def computation (n : Nat) {k : Nat} (hk : 0 < k) :
    TM2ComputableInPolyTime (inputBits (n := n) (k := k)) id outputBits :=
  FiniteWordMachine.computation (inputEnum n k) (defaultInput n hk) outputBits

def machine_output {n k : Nat} (hk : 0 < k) (data : Input n k) :
    TM2OutputsInTime (computation n hk).tm (inputBits data) (some (outputBits data)) 1 := by
  have h := (computation n hk).outputsFun data
  change TM2OutputsInTime (computation n hk).tm ((inputBits data).map id)
    (some ((outputBits data).map id)) ((1 : Polynomial Nat).eval _) at h
  rw [Polynomial.eval_one] at h
  exact Eq.mp (congrArg₂
    (fun (i o : List Bool) => TM2OutputsInTime (computation n hk).tm i (some o) 1)
    (List.map_id (inputBits data)) (List.map_id (outputBits data))) h

def recoverKey {n k : Nat} (side : Side) (slots : Fin n → MixedSupport.Slot)
    (data : Input n k) : Key n :=
  ⟨side, CanonicalKeyShape.retained slots (inputModes data), inputPartition data⟩

theorem recoverKey_input {n k : Nat} (side : Side) (slots : Fin n → MixedSupport.Slot)
    (f : MixedSupport.Assignment slots → Fin k) :
    recoverKey side slots (CanonicalKeyShape.input slots f) = CanonicalKeys.key side slots f := by
  simp only [recoverKey, CanonicalKeys.key, inputModes_recover, inputPartition_eq]

theorem recoverKey_of_same_output {n k : Nat} (side : Side)
    (slots : Fin n → MixedSupport.Slot) (a b : Input n k)
    (same : outputBits a = outputBits b) : recoverKey side slots a = recoverKey side slots b := by
  obtain ⟨hm, hp⟩ := (outputBits_eq_iff a b).mp same
  simp only [recoverKey, hm, hp]

theorem workAlphabet_finite (n : Nat) {k : Nat} (hk : 0 < k)
    (tape : (computation n hk).tm.K) : Finite ((computation n hk).tm.Γ tape) := by
  change Finite Bool
  infer_instance

end
end PerfectCompleteness.CanonicalKeyShapeMachine


namespace PerfectCompleteness.CanonicalOnlineNames

open CanonicalKeys

section Lists

variable {α : Type*} [BEq α] [LawfulBEq α]

theorem firstIndex_append_current (earlier suffix : List α) (key : α) :
    (earlier ++ [key]).idxOf key = (earlier ++ key :: suffix).idxOf key := by
  have present : key ∈ earlier ++ [key] := by simp
  have found := List.idxOf_append_of_mem (l₂ := suffix) present
  simpa only [List.append_assoc, List.singleton_append] using found.symm

theorem firstIndex_le_prefix (earlier : List α) (key : α) :
    (earlier ++ [key]).idxOf key ≤ earlier.length := by
  have found := List.idxOf_lt_length_of_mem (by simp : key ∈ earlier ++ [key])
  simp only [List.length_append, List.length_singleton] at found
  omega

theorem firstIndex_eq_prefix (earlier : List α) (key : α) :
    (earlier ++ [key]).idxOf key = earlier.idxOf key := by
  classical
  by_cases present : key ∈ earlier
  · exact List.idxOf_append_of_mem present
  · rw [List.idxOf_append_of_notMem present, List.idxOf_of_notMem present]
    simp

end Lists

noncomputable section

variable {n : Nat}

def onlineID (earlier : List (Key n)) (key : Key n) : Nat :=
  (BinaryNameSearch.payloads (CanonicalVertexNames.tokens (earlier ++ [key]))).idxOf
    (CanonicalVertexNames.payload key)

theorem tokens_append_current (earlier : List (Key n)) (key : Key n) :
    CanonicalVertexNames.tokens (earlier ++ [key]) =
      CanonicalVertexNames.tokens earlier ++ [(false, CanonicalVertexNames.payload key)] := by
  simp only [CanonicalVertexNames.tokens, List.map_append, List.map_cons, List.map_nil]

theorem current_payload_mem (earlier : List (Key n)) (key : Key n) :
    CanonicalVertexNames.payload key ∈
      BinaryNameSearch.payloads (CanonicalVertexNames.tokens (earlier ++ [key])) :=
  CanonicalVertexNames.payload_mem _ _ (by simp)

theorem dictionary_canonical (earlier : List (Key n)) (key : Key n) :
    ∀ token ∈ CanonicalVertexNames.tokens (earlier ++ [key]),
      BinaryNameMachine.canonical token.2 = true :=
  CanonicalVertexNames.tokens_canonical _

theorem onlineID_le_prefix (earlier : List (Key n)) (key : Key n) :
    onlineID earlier key ≤ earlier.length := by
  have bound := firstIndex_le_prefix (earlier.map CanonicalVertexNames.payload)
    (CanonicalVertexNames.payload key)
  simpa only [onlineID, CanonicalVertexNames.tokens_payloads, List.map_append,
    List.map_cons, List.map_nil, List.length_map] using bound

theorem onlineID_eq_global (earlier suffix : List (Key n)) (key : Key n) :
    onlineID earlier key =
      (BinaryNameSearch.payloads
        (CanonicalVertexNames.tokens (earlier ++ key :: suffix))).idxOf
          (CanonicalVertexNames.payload key) := by
  simpa only [onlineID, CanonicalVertexNames.tokens_payloads, List.map_append,
    List.map_cons, List.map_nil] using
      firstIndex_append_current (earlier.map CanonicalVertexNames.payload)
        (suffix.map CanonicalVertexNames.payload) (CanonicalVertexNames.payload key)

theorem onlineID_eq_name_val (earlier suffix : List (Key n)) (key : Key n) :
    onlineID earlier key =
      (CanonicalVertexNames.name (earlier ++ key :: suffix) key (by simp)).val :=
  onlineID_eq_global earlier suffix key

theorem onlineID_eq_prefix_index (earlier : List (Key n)) (key : Key n) :
    onlineID earlier key =
      (BinaryNameSearch.payloads (CanonicalVertexNames.tokens earlier)).idxOf
        (CanonicalVertexNames.payload key) := by
  simpa only [onlineID, CanonicalVertexNames.tokens_payloads, List.map_append,
    List.map_cons, List.map_nil] using
      firstIndex_eq_prefix (earlier.map CanonicalVertexNames.payload)
        (CanonicalVertexNames.payload key)

theorem onlineID_repeat (earlier middle : List (Key n)) (key : Key n) :
    onlineID (earlier ++ key :: middle) key = onlineID earlier key := by
  calc
    _ = (BinaryNameSearch.payloads
        (CanonicalVertexNames.tokens (earlier ++ key :: middle))).idxOf
          (CanonicalVertexNames.payload key) := onlineID_eq_prefix_index _ key
    _ = _ := (onlineID_eq_global earlier middle key).symm

theorem onlineID_eq_iff_same_final (keys prefixA suffixA prefixB suffixB : List (Key n))
    (a b : Key n)
    (first : keys = prefixA ++ a :: suffixA)
    (second : keys = prefixB ++ b :: suffixB) :
    onlineID prefixA a = onlineID prefixB b ↔ a = b := by
  have presentA : a ∈ keys := by rw [first]; simp
  rw [onlineID_eq_global prefixA suffixA a, onlineID_eq_global prefixB suffixB b,
    ← first, ← second]
  constructor
  · intro same
    apply CanonicalVertexNames.payload_injective n
    exact (List.idxOf_inj (CanonicalVertexNames.payload_mem keys a presentA)).mp same
  · intro same
    subst b
    rfl

def onlineName (earlier : List (Key n)) (key : Key n) : Fin (earlier.length + 1) :=
  ⟨onlineID earlier key, by have := onlineID_le_prefix earlier key; omega⟩

@[simp] theorem onlineName_val (earlier : List (Key n)) (key : Key n) :
    (onlineName earlier key).val = onlineID earlier key := rfl

def paddedName (keys : List (Key n)) (vertices : Nat) (enough : keys.length ≤ vertices)
    (key : Key n) (present : key ∈ keys) : Fin vertices :=
  ⟨(CanonicalVertexNames.name keys key present).val,
    lt_of_lt_of_le (CanonicalVertexNames.name keys key present).isLt enough⟩

@[simp] theorem paddedName_val (keys : List (Key n)) (vertices : Nat)
    (enough : keys.length ≤ vertices) (key : Key n) (present : key ∈ keys) :
    (paddedName keys vertices enough key present).val =
      (CanonicalVertexNames.name keys key present).val := rfl

theorem paddedName_eq_iff (keys : List (Key n)) (vertices : Nat)
    (enough : keys.length ≤ vertices) (a b : Key n) (ha : a ∈ keys) (hb : b ∈ keys) :
    paddedName keys vertices enough a ha = paddedName keys vertices enough b hb ↔ a = b := by
  constructor
  · intro same
    apply (CanonicalVertexNames.name_eq_iff keys a b ha hb).mp
    apply Fin.ext
    exact congrArg (fun value : Fin vertices => value.val) same
  · intro same
    subst b
    rfl

def paddedEmbedding (keys : List (Key n)) (vertices : Nat) (enough : keys.length ≤ vertices) :
    {key // key ∈ keys} ↪ Fin vertices where
  toFun key := paddedName keys vertices enough key.val key.property
  inj' := by
    intro a b same
    exact Subtype.ext ((paddedName_eq_iff keys vertices enough
      a.val b.val a.property b.property).mp same)

def onlinePaddedName (earlier : List (Key n)) (key : Key n) (vertices : Nat)
    (room : earlier.length < vertices) : Fin vertices :=
  ⟨onlineID earlier key, lt_of_le_of_lt (onlineID_le_prefix earlier key) room⟩

theorem onlinePaddedName_eq_final (earlier suffix : List (Key n)) (key : Key n)
    (vertices : Nat) (enough : (earlier ++ key :: suffix).length ≤ vertices) :
    onlinePaddedName earlier key vertices (by
      simp only [List.length_append, List.length_cons] at enough
      omega) =
      paddedName (earlier ++ key :: suffix) vertices enough key (by simp) := by
  apply Fin.ext
  exact onlineID_eq_name_val earlier suffix key

end
end PerfectCompleteness.CanonicalOnlineNames

end OAI
