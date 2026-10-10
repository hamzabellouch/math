import OAI.Computability.PerfectCompleteness.Machines.BinaryNameSearch
import OAI.Computability.PerfectCompleteness.Machines.FiniteBlockMachineLemmas

namespace OAI


namespace PerfectCompleteness.CanonicalVertexNames

open CanonicalKeys
open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

noncomputable section

variable {n : Nat}

def payload (key : Key n) : List Bool := CanonicalKeyEncoding.bits key ++ [true]

theorem payload_injective (n : Nat) : Function.Injective (payload (n := n)) := by
  intro a b h
  exact CanonicalKeyEncoding.bits_injective n (List.append_cancel_right h)

private theorem finalDigit_append_true (bits : List Bool) (previous : Option Bool) :
    BinaryNameMachine.finalDigit (bits ++ [true]) previous = some true := by
  induction bits generalizing previous with
  | nil => rfl
  | cons bit bits ih => exact ih (some bit)

@[simp] theorem payload_canonical (key : Key n) :
    BinaryNameMachine.canonical (payload key) = true := by
  simp [payload, BinaryNameMachine.canonical, finalDigit_append_true]

@[simp] theorem payload_length (key : Key n) :
    (payload key).length = (CanonicalKeyEncoding.bits key).length + 1 := by
  simp only [payload, List.length_append, List.length_cons, List.length_nil]

def tokens (keys : List (Key n)) : List BinaryNameSearch.Token :=
  keys.map (fun key => (false, payload key))

@[simp] theorem tokens_length (keys : List (Key n)) :
    (tokens keys).length = keys.length := by
  simp only [tokens, List.length_map]

@[simp] theorem tokens_payloads (keys : List (Key n)) :
    BinaryNameSearch.payloads (tokens keys) = keys.map payload := by
  simp only [BinaryNameSearch.payloads, tokens, List.map_map, Function.comp_def]

theorem payload_mem (keys : List (Key n)) (key : Key n) (hmem : key ∈ keys) :
    payload key ∈ BinaryNameSearch.payloads (tokens keys) := by
  rw [tokens_payloads]
  exact List.mem_map.mpr ⟨key, hmem, rfl⟩

theorem tokens_canonical (keys : List (Key n)) :
    ∀ token ∈ tokens keys, BinaryNameMachine.canonical token.2 = true := by
  intro token htoken
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp htoken
  exact payload_canonical key

def name (keys : List (Key n)) (key : Key n) (hmem : key ∈ keys) : Fin keys.length :=
  ⟨(BinaryNameSearch.payloads (tokens keys)).idxOf (payload key), by
    have h := List.idxOf_lt_length_of_mem (payload_mem keys key hmem)
    simpa only [tokens_payloads, List.length_map] using h⟩

@[simp] theorem name_val (keys : List (Key n)) (key : Key n) (hmem : key ∈ keys) :
    (name keys key hmem).val =
      (BinaryNameSearch.payloads (tokens keys)).idxOf (payload key) := rfl

theorem name_eq_iff (keys : List (Key n)) (a b : Key n)
    (ha : a ∈ keys) (hb : b ∈ keys) : name keys a ha = name keys b hb ↔ a = b := by
  constructor
  · intro h
    have hidx := congrArg Fin.val h
    exact payload_injective n ((List.idxOf_inj (payload_mem keys a ha)).mp hidx)
  · intro h
    subst b
    rfl

theorem name_injective (keys : List (Key n)) :
    Function.Injective (fun key : {key // key ∈ keys} => name keys key.val key.property) := by
  intro a b h
  exact Subtype.ext ((name_eq_iff keys a.val b.val a.property b.property).mp h)

def embedding (keys : List (Key n)) : {key // key ∈ keys} ↪ Fin keys.length :=
  ⟨fun key => name keys key.val key.property, name_injective keys⟩

def payloadBound (n bound : Nat) : Nat :=
  (1 + 2 ^ (11 ^ n) + 6 * n) * (max n (max bound 2) + 1) + 1

theorem payload_length_le (key : Key n) (bound : Nat)
    (hretained : key.retained.length ≤ n)
    (hIDs : ∀ entry ∈ key.retained, KeyMetadataEncoding.entryID entry.2 ≤ bound) :
    (payload key).length ≤ payloadBound n bound := by
  rw [payload_length]
  unfold payloadBound
  apply Nat.add_le_add_right
  apply (CanonicalKeyEncoding.bits_length_le key bound hIDs).trans
  apply Nat.mul_le_mul_right
  rw [CanonicalKeyEncoding.partitionWidth_eq]
  omega

theorem payloadSize_le (keys : List (Key n)) (B : Nat)
    (hbound : ∀ key ∈ keys, (payload key).length ≤ B) :
    BinaryNameSearch.payloadSize (tokens keys) ≤ B * keys.length := by
  revert hbound
  induction keys with
  | nil =>
      intro _
      exact Nat.le_refl 0
  | cons key keys ih =>
      intro hbound
      have hhead := hbound key (by simp)
      have htail := ih (fun k hk => hbound k (List.mem_cons_of_mem key hk))
      change (payload key).length + BinaryNameSearch.payloadSize (tokens keys) ≤
        B * (keys.length + 1)
      apply (Nat.add_le_add hhead htail).trans_eq
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_comm _ _

theorem stream_length_le (keys : List (Key n)) (bound : Nat)
    (hretained : ∀ key ∈ keys, key.retained.length ≤ n)
    (hIDs : ∀ key ∈ keys, ∀ entry ∈ key.retained,
      KeyMetadataEncoding.entryID entry.2 ≤ bound) :
    (BinaryNameSearch.stream (tokens keys)).length ≤
      (2 * payloadBound n bound + 2) * keys.length := by
  have hsize := payloadSize_le keys (payloadBound n bound)
    (fun key hk => payload_length_le key bound (hretained key hk) (hIDs key hk))
  rw [BinaryNameSearch.stream_length, tokens_length]
  calc
    _ ≤ 2 * (payloadBound n bound * keys.length) + 2 * keys.length :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 hsize) _
    _ = _ := by rw [Nat.add_mul, Nat.mul_assoc]


variable {K Λ A : Type} [DecidableEq K]

def searchInTime (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (labels : BinaryNameSearch.Label → Λ) (foundExit missingExit malformedExit : Option Λ)
    (program : Λ → TM2.Stmt (BinaryNameSearch.Alphabet (K := K)) Λ
      (BinaryNameSearch.State A))
    (atLabels : ∀ l, program (labels l) =
      BinaryNameSearch.instruction tape labels foundExit missingExit malformedExit l)
    (base : K → List Bool) (ambient : A)
    (keys : List (Key n)) (key : Key n) (hmem : key ∈ keys)
    (suffix counter : List Bool)
    (keyWord : base (tape 1) = (payload key).reverse)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) (bound : Nat)
    (hretained : ∀ k ∈ keys, k.retained.length ≤ n)
    (hIDs : ∀ k ∈ keys, ∀ entry ∈ k.retained,
      KeyMetadataEncoding.entryID entry.2 ≤ bound) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .sign), BinaryNameSearch.clean ambient,
        tapesAt (tape 0) (tape 5) base
          (BinaryNameSearch.stream (tokens keys) ++ suffix) counter⟩
      (some ⟨foundExit, BinaryNameSearch.clean ambient,
        tapesAt (tape 0) (tape 5) base
          (BinaryNameSearch.stream (BinaryNameSearch.afterMatch (tokens keys) (payload key)) ++
            suffix)
          (List.replicate (name keys key hmem).val true ++ counter)⟩)
      ((3 * payloadBound n bound + 7) *
        ((2 * payloadBound n bound + 2) * keys.length)) := by
  let run := BinaryNameSearch.searchInTime tape distinct labels
    foundExit missingExit malformedExit program atLabels base ambient
    (tokens keys) (payload key) suffix counter (tokens_canonical keys)
    (payload_mem keys key hmem) keyWord candidateEmpty copyEmpty scratchEmpty
  have hkey := payload_length_le key bound (hretained key hmem) (hIDs key hmem)
  have hstream := stream_length_le keys bound hretained hIDs
  exact
    { steps := run.steps
      evals_in_steps := run.evals_in_steps
      steps_le_m := run.steps_le_m.trans (Nat.mul_le_mul (by omega) hstream) }

end
end PerfectCompleteness.CanonicalVertexNames

end OAI
