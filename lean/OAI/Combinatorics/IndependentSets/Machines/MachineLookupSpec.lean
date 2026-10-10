import Mathlib
import OAI.Combinatorics.IndependentSets.Encoding.Target

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineLookupSpec

def skipWord : List Bool → List Bool
  | [] => []
  | true :: bs => skipWord bs
  | false :: bs => bs

@[simp] theorem skipWord_encodeWord (n : Nat) (bs : List Bool) :
    skipWord (encodeWord n ++ bs) = bs := by
  induction n with
  | zero => simp [encodeWord, skipWord]
  | succ n ih =>
    simpa [encodeWord, List.replicate_succ, skipWord] using ih

theorem skipWord_iterate_encodeWords (i : Nat) (values : List Nat) :
    (skipWord^[i]) (encodeWords values) = encodeWords (values.drop i) := by
  induction i generalizing values with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases values with
    | nil => simpa [encodeWords, skipWord] using ih []
    | cons n ns =>
      simpa only [encodeWords, skipWord_encodeWord, List.drop_succ_cons] using ih ns

def headWord : List Bool → Option (List Bool)
  | [] => none
  | false :: _ => some [false]
  | true :: bs => (headWord bs).map (true :: ·)

@[simp] theorem headWord_encodeWord (n : Nat) (bs : List Bool) :
    headWord (encodeWord n ++ bs) = some (encodeWord n) := by
  induction n with
  | zero => simp [encodeWord, headWord]
  | succ n ih =>
    simpa [encodeWord, List.replicate_succ, headWord] using
      congrArg (Option.map (true :: ·)) ih

@[simp] theorem headWord_encodeWords (values : List Nat) :
    headWord (encodeWords values) = values.head?.map encodeWord := by
  cases values with
  | nil => rfl
  | cons n ns => exact headWord_encodeWord n (encodeWords ns)

def lookupBits (i : Nat) (table : List Bool) : Option (List Bool) :=
  headWord ((skipWord^[i]) table)

@[simp] theorem lookupBits_encodeWords (i : Nat) (values : List Nat) :
    lookupBits i (encodeWords values) = values[i]?.map encodeWord := by
  rw [lookupBits, skipWord_iterate_encodeWords, headWord_encodeWords,
    List.head?_drop]

def lookupEncoded (index table : List Bool) : Option (List Bool) :=
  match decodeWords index with
  | some [i] => lookupBits i table
  | _ => none

@[simp] theorem decodeWords_encodeWord (i : Nat) :
    decodeWords (encodeWord i) = some [i] := by
  simpa [encodeWords] using decodeWords_encodeWords [i]

@[simp] theorem lookupEncoded_encode (i : Nat) (values : List Nat) :
    lookupEncoded (encodeWord i) (encodeWords values) =
      values[i]?.map encodeWord := by
  simp [lookupEncoded]

theorem lookupEncoded_some (i value : Nat) (values : List Nat)
    (h : values[i]? = some value) :
    lookupEncoded (encodeWord i) (encodeWords values) = some (encodeWord value) := by
  simp [h]

theorem lookupEncoded_none (i : Nat) (values : List Nat)
    (h : values.length ≤ i) :
    lookupEncoded (encodeWord i) (encodeWords values) = none := by
  simp [List.getElem?_eq_none h]

theorem encoded_selected_split (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    encodeWords values = encodeWords (values.take i) ++ encodeWord value ++
      encodeWords (values.drop (i + 1)) := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hv⟩
  have hs : values = values.take i ++ value :: values.drop (i + 1) := by
    calc
      values = values.take i ++ values.drop i := (List.take_append_drop i values).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hi, hv]
  simpa only [encodeWords_append, encodeWords, List.append_assoc] using
    congrArg encodeWords hs

def scannedBits (values : List Nat) (i : Nat) : Nat :=
  (encodeWords (values.take (i + 1))).length

theorem encoded_prefix_length_le (values : List Nat) (i : Nat) :
    (encodeWords (values.take i)).length ≤ (encodeWords values).length := by
  have hs : encodeWords (values.take i) ++ encodeWords (values.drop i) =
      encodeWords values := by
    rw [← encodeWords_append, List.take_append_drop]
  have hl := congrArg List.length hs
  simp only [List.length_append] at hl
  omega

theorem scannedBits_le (values : List Nat) (i : Nat) :
    scannedBits values i ≤ (encodeWords values).length :=
  encoded_prefix_length_le values (i + 1)

theorem scannedBits_of_some (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    scannedBits values i = (encodeWords (values.take i)).length + value + 1 := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hv⟩
  simp [scannedBits, List.take_succ_eq_append_getElem hi, hv, encodeWords,
    Nat.add_assoc]

theorem selected_scan_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWords (values.take i)).length + value + 1 ≤
      (encodeWords values).length := by
  rw [← scannedBits_of_some values i value h]
  exact scannedBits_le values i

theorem output_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWord value).length ≤ (encodeWords values).length := by
  have hs := selected_scan_length_le values i value h
  rw [encodeWord_length]
  omega

theorem index_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWord i).length ≤ (encodeWords values).length := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩
  have hp : i ≤ (encodeWords (values.take i)).length := by
    simp only [encodeWords_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    omega
  have hs := selected_scan_length_le values i value h
  rw [encodeWord_length]
  omega

def steps : List Nat → Nat → Nat
  | [], i => 2 * i + 2
  | n :: _, 0 => n + 3
  | n :: ns, i + 1 => n + 2 + steps ns i

theorem steps_le_encoded_length_strong (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * i + 2 := by
  induction values generalizing i with
  | nil => simp [steps, encodeWords]
  | cons n ns ih =>
    cases i with
    | zero =>
      simp only [steps, encodeWords, List.length_append, encodeWord_length]
      omega
    | succ i =>
      have ht := ih i
      simp only [steps, encodeWords, List.length_append, encodeWord_length]
      omega

theorem steps_le_encoded_length (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * i + 3 := by
  have h := steps_le_encoded_length_strong values i
  omega

theorem steps_eq_scannedBits_of_lt (values : List Nat) (i : Nat)
    (h : i < values.length) :
    steps values i = scannedBits values i + i + 2 := by
  induction values generalizing i with
  | nil => simp at h
  | cons n ns ih =>
    cases i with
    | zero => simp [steps, scannedBits, encodeWords, Nat.add_assoc]
    | succ i =>
      have ht := ih i (by simpa using h)
      simp only [scannedBits] at ht
      simp only [steps, scannedBits, List.take_succ_cons, encodeWords,
        List.length_append, encodeWord_length]
      omega

theorem steps_eq_scannedBits_of_some (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    steps values i = scannedBits values i + i + 2 := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩
  exact steps_eq_scannedBits_of_lt values i hi

theorem steps_add_length_of_invalid (values : List Nat) (i : Nat)
    (h : values.length ≤ i) :
    steps values i + values.length = (encodeWords values).length + 2 * i + 2 := by
  induction values generalizing i with
  | nil => simp [steps, encodeWords]
  | cons n ns ih =>
    cases i with
    | zero => simp at h
    | succ i =>
      have ht := ih i (by simpa using h)
      simp only [steps, encodeWords, List.length_append, encodeWord_length,
        List.length_cons]
      omega

theorem steps_le_input_encoding_size (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * (encodeWord i).length := by
  have h := steps_le_encoded_length_strong values i
  rw [encodeWord_length]
  omega

end IndependentSetsGames.Foundations.Complexity.MachineLookupSpec

end OAI
