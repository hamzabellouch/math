import OAI.Combinatorics.EditApproximation.Binary.BinaryMemo

namespace OAI

/-! Persistent dictionary requests. A fresh oracle is called only on a
cache miss; subsequent requests preserve and return the stored answer. -/

namespace EditApproximation

structure MemoRequestResult where
  value : ℚ
  memory : BinaryMemo ℚ
  fresh : Bool
  dictionaryVisits : ℕ

section Requests

variable {ι : Type*} (bits : ℕ) (encode : ι → ℕ) (oracle : ι → ℚ)

def memoRequest (memory : BinaryMemo ℚ) (key : ι) : MemoRequestResult :=
  let found := memory.lookupCosted (binaryMemoKey bits (encode key))
  match found.1 with
  | some value => ⟨value, memory, false, found.2⟩
  | none =>
    let value := oracle key
    let stored := memory.insertCosted (binaryMemoKey bits (encode key)) value
    ⟨value, stored.1, true, found.2 + stored.2⟩

theorem memoRequest_lookup (memory : BinaryMemo ℚ) (key : ι) :
    (memoRequest bits encode oracle memory key).memory.lookup (binaryMemoKey bits (encode key)) =
      some (memoRequest bits encode oracle memory key).value := by
  simp only [memoRequest, BinaryMemo.lookupCosted_spec]
  split <;> simp_all only [BinaryMemo.insertCosted_spec, BinaryMemo.lookup_insert_same]

theorem memoRequest_preserves (memory : BinaryMemo ℚ) (key other : ι) (value : ℚ)
    (hold : memory.lookup (binaryMemoKey bits (encode other)) = some value) :
    (memoRequest bits encode oracle memory key).memory.lookup (binaryMemoKey bits (encode other)) = some value := by
  simp only [memoRequest, BinaryMemo.lookupCosted_spec]
  split
  · exact hold
  · rename_i hnone
    simp only [BinaryMemo.insertCosted_spec]
    apply (BinaryMemo.lookup_insert_other _ _ _ _ ?_).trans hold
    intro heq
    rw [heq, hnone] at hold
    cases hold

theorem memoRequest_fresh_iff (memory : BinaryMemo ℚ) (key : ι) :
    (memoRequest bits encode oracle memory key).fresh = true ↔
      memory.lookup (binaryMemoKey bits (encode key)) = none := by
  simp only [memoRequest, BinaryMemo.lookupCosted_spec]
  split <;> simp_all

theorem memoRequest_visits (memory : BinaryMemo ℚ) (key : ι) :
    (memoRequest bits encode oracle memory key).dictionaryVisits ≤ 2 * (bits + 1) := by
  simp only [memoRequest, BinaryMemo.lookupCosted_spec]
  split
  · simp only [binaryMemoKey_length]
    omega
  · simp only [BinaryMemo.insertCosted_spec, binaryMemoKey_length]
    omega

def memoSound (memory : BinaryMemo ℚ) : Prop :=
  ∀ key value, memory.lookup (binaryMemoKey bits (encode key)) = some value → value = oracle key

theorem memoRequest_sound (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode oracle memory) (key : ι) :
    (memoRequest bits encode oracle memory key).value = oracle key ∧
      memoSound bits encode oracle (memoRequest bits encode oracle memory key).memory := by
  simp only [memoRequest, BinaryMemo.lookupCosted_spec]
  split
  · rename_i value hvalue
    exact ⟨hsound key value hvalue, hsound⟩
  · simp only [BinaryMemo.insertCosted_spec]
    refine ⟨True.intro, ?_⟩
    intro other value hvalue
    rw [binaryMemo_lookup_insert _ bits (encode key) (encode other)
      (hbounded key) (hbounded other)] at hvalue
    split_ifs at hvalue with heq
    · have heqkey := hinjective heq
      cases heqkey
      exact Option.some.inj hvalue.symm
    · exact hsound other value hvalue

structure MemoBatchResult (ι : Type*) where
  values : List ℚ
  memory : BinaryMemo ℚ
  freshKeys : List ι
  dictionaryVisits : ℕ

def memoRequests (memory : BinaryMemo ℚ) : List ι → MemoBatchResult ι
  | [] => ⟨[], memory, [], 0⟩
  | key :: rest =>
    let first := memoRequest bits encode oracle memory key
    let remaining := memoRequests first.memory rest
    ⟨first.value :: remaining.values, remaining.memory,
      (if first.fresh then [key] else []) ++ remaining.freshKeys,
      first.dictionaryVisits + remaining.dictionaryVisits⟩

theorem memoRequests_preserves (memory : BinaryMemo ℚ) (keys : List ι) (key : ι) (value : ℚ)
    (hold : memory.lookup (binaryMemoKey bits (encode key)) = some value) :
    (memoRequests bits encode oracle memory keys).memory.lookup (binaryMemoKey bits (encode key)) = some value := by
  induction keys generalizing memory with
  | nil => exact hold
  | cons first rest ih =>
    exact ih _ (memoRequest_preserves bits encode oracle memory first key value hold)

theorem memoRequests_fresh_absent (memory : BinaryMemo ℚ) (keys : List ι) (key : ι)
    (hfresh : key ∈ (memoRequests bits encode oracle memory keys).freshKeys) :
    memory.lookup (binaryMemoKey bits (encode key)) = none := by
  induction keys generalizing memory with
  | nil => cases hfresh
  | cons first rest ih =>
    simp only [memoRequests, List.mem_append] at hfresh
    rcases hfresh with hfirst | hrest
    · split_ifs at hfirst with hf
      · have heq : key = first := by simpa only [List.mem_singleton] using hfirst
        subst key
        exact (memoRequest_fresh_iff bits encode oracle memory first).1 hf
      · cases hfirst
    · have hafter := ih _ hrest
      cases hbefore : memory.lookup (binaryMemoKey bits (encode key)) with
      | none => rfl
      | some value =>
        have hkeep := memoRequest_preserves bits encode oracle memory first key value hbefore
        rw [hafter] at hkeep
        cases hkeep

theorem memoRequests_fresh_nodup [DecidableEq ι] (memory : BinaryMemo ℚ) (keys : List ι) :
    (memoRequests bits encode oracle memory keys).freshKeys.Nodup := by
  induction keys generalizing memory with
  | nil => exact List.nodup_nil
  | cons first rest ih =>
    simp only [memoRequests]
    split_ifs with hf
    · rw [List.singleton_append, List.nodup_cons]
      refine ⟨?_, ih _⟩
      intro hmem
      have hnone := memoRequests_fresh_absent bits encode oracle _ rest first hmem
      have hsome := memoRequest_lookup bits encode oracle memory first
      rw [hnone] at hsome
      cases hsome
    · exact ih _

theorem memoRequests_fresh_subset (memory : BinaryMemo ℚ) (keys : List ι) :
    ∀ key ∈ (memoRequests bits encode oracle memory keys).freshKeys, key ∈ keys := by
  induction keys generalizing memory with
  | nil => intro key hmem; cases hmem
  | cons first rest ih =>
    intro key hmem
    simp only [memoRequests, List.mem_append] at hmem
    rcases hmem with hfirst | hrest
    · split_ifs at hfirst
      · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hfirst))
      · cases hfirst
    · exact List.mem_cons_of_mem first (ih _ key hrest)

theorem memoRequests_fresh_count [DecidableEq ι] (memory : BinaryMemo ℚ) (keys : List ι) :
    (memoRequests bits encode oracle memory keys).freshKeys.length ≤ keys.toFinset.card := by
  rw [← List.toFinset_card_of_nodup (memoRequests_fresh_nodup bits encode oracle memory keys)]
  apply Finset.card_le_card
  intro key hkey
  exact List.mem_toFinset.mpr (memoRequests_fresh_subset bits encode oracle memory keys key
    (List.mem_toFinset.mp hkey))

theorem memoRequests_visits (memory : BinaryMemo ℚ) (keys : List ι) :
    (memoRequests bits encode oracle memory keys).dictionaryVisits ≤ keys.length * (2 * (bits + 1)) := by
  induction keys generalizing memory with
  | nil => simp only [memoRequests, List.length_nil, Nat.zero_mul, le_refl]
  | cons first rest ih =>
    have hfirst := memoRequest_visits bits encode oracle memory first
    have hrest := ih (memoRequest bits encode oracle memory first).memory
    simpa only [memoRequests, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
      Nat.add_le_add hfirst hrest

theorem memoSound_empty : memoSound bits encode oracle .empty := by
  intro key value hvalue
  rw [BinaryMemo.lookup_empty] at hvalue
  cases hvalue

theorem memoRequests_sound (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode oracle memory) (keys : List ι) :
    (memoRequests bits encode oracle memory keys).values = keys.map oracle ∧
      memoSound bits encode oracle (memoRequests bits encode oracle memory keys).memory := by
  induction keys generalizing memory with
  | nil => exact ⟨rfl, hsound⟩
  | cons first rest ih =>
    have hf := memoRequest_sound bits encode oracle hinjective hbounded memory hsound first
    have hr := ih _ hf.2
    exact ⟨congrArg₂ List.cons hf.1 hr.1, hr.2⟩

end Requests

end EditApproximation

end OAI
