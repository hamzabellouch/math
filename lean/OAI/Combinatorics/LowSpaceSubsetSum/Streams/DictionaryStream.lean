import OAI.Combinatorics.LowSpaceSubsetSum.Streams.BoundedDictionary
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.RowMerge

namespace OAI

/-!
# A bounded dictionary driven by a stream cursor

The executable loop reads one key, updates the trie and its counters, and
tail-calls with the next cursor. Lists and finite key sets below are proof
views only; the loop stores neither a trace nor a set of all possible keys.
-/

namespace LowSpaceSubsetSum.BinaryTrie

def keySet : Tree → Finset (List Bool)
  | .empty => ∅
  | .leaf => {[]}
  | .node zero one => (keySet zero).image (List.cons false) ∪
      (keySet one).image (List.cons true)

theorem mem_keySet (t : Tree) (key : List Bool) :
    key ∈ keySet t ↔ contains t key = true := by
  induction t generalizing key with
  | empty => simp [keySet, contains]
  | leaf => cases key <;> simp [keySet, contains]
  | node zero one ih0 ih1 =>
    cases key with
    | nil => simp [keySet, contains]
    | cons b key => cases b <;> simp [keySet, contains, ih0, ih1]

theorem card_keySet (t : Tree) : (keySet t).card = entries t := by
  induction t with
  | empty => simp [keySet, entries]
  | leaf => simp [keySet, entries]
  | node zero one ih0 ih1 =>
    have hd : Disjoint ((keySet zero).image (List.cons false))
        ((keySet one).image (List.cons true)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
      cases hb
    rw [keySet, Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2),
      Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2), ih0, ih1]
    rfl

theorem keySet_width {t : Tree} {width : ℕ} (ht : HasWidth t width)
    {key : List Bool} (hk : key ∈ keySet t) : key.length = width := by
  induction t generalizing width key with
  | empty => simp [keySet] at hk
  | leaf =>
    have hkey : key = [] := by simpa [keySet] using hk
    rw [hkey]
    exact ht.symm
  | node zero one ih0 ih1 =>
    cases width with
    | zero => exact ht.elim
    | succ width =>
      rcases Finset.mem_union.mp hk with h | h
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
        simp [ih0 ht.1 hq]
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
        simp [ih1 ht.2 hq]

theorem keySet_insert {t : Tree} {key : List Bool} {width : ℕ}
    (ht : HasWidth t width) (hk : key.length = width) :
    keySet (insert t key) = Insert.insert key (keySet t) := by
  ext query
  by_cases hq : query.length = width
  · rw [mem_keySet, contains_insert_iff ht hk hq, Finset.mem_insert, mem_keySet]
  · have hnew : query ∉ keySet (insert t key) :=
      fun h => hq (keySet_width (insert_hasWidth ht hk) h)
    have hold : query ∉ keySet t := fun h => hq (keySet_width ht h)
    have hne : query ≠ key := fun h => hq (by simpa only [h] using hk)
    simp [hnew, hold, hne]

/-- A fitting universe of keys prevents overflow, even when the stream
contains arbitrarily many repetitions. The initial trie may already hold
some keys from that same universe. -/
theorem build_fits_universe {C width : ℕ} {t : Tree} {keys : List (List Bool)}
    {U : Finset (List Bool)} (ht : HasWidth t width)
    (hwidth : ∀ key ∈ U, key.length = width)
    (htU : keySet t ⊆ U) (hkeys : ∀ key ∈ keys, key ∈ U) (hcap : U.card ≤ C) :
    (build C t keys).overflow = false := by
  induction keys generalizing t with
  | nil => rfl
  | cons key rest ih =>
    have hkU := hkeys key (by simp)
    have hk := hwidth key hkU
    have hr : ∀ q ∈ rest, q ∈ U := fun q h => hkeys q (by simp [h])
    have hnextU : keySet (insert t key) ⊆ U := by
      rw [keySet_insert ht hk]
      exact Finset.insert_subset hkU htU
    have hnext : entries (insert t key) ≤ C := by
      rw [← card_keySet]
      exact (Finset.card_le_card hnextU).trans hcap
    simp only [build]
    split
    · exact ih ht htU hr
    · rw [ite_eq_right (by omega)]
      exact ih (insert_hasWidth ht hk) hnextU hr

theorem build_complete_processed {C : ℕ} {t : Tree} {keys : List (List Bool)}
    (h : (build C t keys).overflow = false) :
    (build C t keys).processed = keys.length := by
  induction keys generalizing t with
  | nil => rfl
  | cons key rest ih =>
    by_cases hdup : contains t key = true
    · simp only [build, hdup, ↓reduceIte, tick] at h ⊢
      simpa only [List.length_cons] using congrArg Nat.succ (ih h)
    · have hnew : contains t key = false := Bool.eq_false_iff.mpr hdup
      by_cases hover : C < entries (insert t key)
      · simp [build, hnew, hover] at h
      · simp only [build, hnew, Bool.false_eq_true, ↓reduceIte, hover, tick] at h ⊢
        simpa only [List.length_cons] using congrArg Nat.succ (ih h)

universe u

structure StreamResult (σ : Type u) where
  cursor : σ
  tree : Tree
  overflow : Bool
  processed : ℕ
  queries : ℕ

/-- Tail-recursive implementation. Every recursive call receives the updated
cursor, trie and counters. A capacity violation stops immediately. -/
def run {σ : Type u} (C : ℕ) (read : σ → Option (List Bool × σ)) :
    ℕ → σ → Tree → ℕ → ℕ → StreamResult σ
  | 0, s, t, processed, queries => ⟨s, t, false, processed, queries⟩
  | fuel + 1, s, t, processed, queries =>
    match read s with
    | none => ⟨s, t, false, processed, queries + 1⟩
    | some (key, next) =>
      if contains t key then run C read fuel next t (processed + 1) (queries + 1)
      else
        let t' := insert t key
        if C < entries t' then ⟨next, t', true, processed + 1, queries + 1⟩
        else run C read fuel next t' (processed + 1) (queries + 1)

/-- Finite output trace, used only to state and prove the loop's behavior. -/
def readKeys {σ : Type u} (read : σ → Option (List Bool × σ)) :
    ℕ → σ → List (List Bool)
  | 0, _ => []
  | fuel + 1, s => match read s with
    | none => []
    | some (key, next) => key :: readKeys read fuel next

theorem run_spec {σ : Type u} (C : ℕ) (read : σ → Option (List Bool × σ))
    (fuel : ℕ) (s : σ) (t : Tree) (processed queries : ℕ) :
    let r := run C read fuel s t processed queries
    let b := build C t (readKeys read fuel s)
    r.tree = b.tree ∧ r.overflow = b.overflow ∧ r.processed = processed + b.processed := by
  induction fuel generalizing s t processed queries with
  | zero => simp [run, readKeys, build]
  | succ fuel ih =>
    cases hr : read s with
    | none => simp [run, readKeys, hr, build]
    | some pair =>
      obtain ⟨key, next⟩ := pair
      simp only [run, readKeys, hr, build]
      split
      · obtain ⟨ht, ho, hp⟩ := ih next t (processed + 1) (queries + 1)
        exact ⟨ht, ho, by simpa only [tick] using hp.trans (by omega)⟩
      · split
        · simp
        · obtain ⟨ht, ho, hp⟩ := ih next (insert t key) (processed + 1) (queries + 1)
          exact ⟨ht, ho, by simpa only [tick] using hp.trans (by omega)⟩

theorem run_queries_le {σ : Type u} (C : ℕ) (read : σ → Option (List Bool × σ))
    (fuel : ℕ) (s : σ) (t : Tree) (processed queries : ℕ) :
    (run C read fuel s t processed queries).queries ≤ queries + fuel := by
  induction fuel generalizing s t processed queries with
  | zero => simp [run]
  | succ fuel ih =>
    cases hr : read s with
    | none => simp [run, hr]
    | some pair =>
      obtain ⟨key, next⟩ := pair
      simp only [run, hr]
      split
      · exact (ih next t (processed + 1) (queries + 1)).trans (by omega)
      · split
        · simp
        · exact (ih next (insert t key) (processed + 1) (queries + 1)).trans (by omega)

/-- At most one reader query is spent detecting the end of the stream.
The bound also holds for an overflow stop or an exhausted fuel budget. -/
theorem run_queries_processed {σ : Type u} (C : ℕ)
    (read : σ → Option (List Bool × σ)) (fuel : ℕ) (s : σ) (t : Tree)
    (processed queries : ℕ) :
    (run C read fuel s t processed queries).queries + processed ≤
      queries + (run C read fuel s t processed queries).processed + 1 := by
  induction fuel generalizing s t processed queries with
  | zero => simp [run]
  | succ fuel ih =>
    cases hr : read s with
    | none => simp [run, hr, Nat.add_comm, Nat.add_assoc]
    | some pair =>
      obtain ⟨key, next⟩ := pair
      simp only [run, hr]
      split
      · have h := ih next t (processed + 1) (queries + 1)
        omega
      · split
        · simp [Nat.add_comm, Nat.add_left_comm]
        · have h := ih next (insert t key) (processed + 1) (queries + 1)
          omega

def advance {σ : Type u} (read : σ → Option (List Bool × σ)) : ℕ → σ → σ
  | 0, s => s
  | count + 1, s => match read s with
    | none => s
    | some (_, next) => advance read count next

theorem run_cursor {σ : Type u} (C : ℕ) (read : σ → Option (List Bool × σ))
    (fuel : ℕ) (s : σ) (t : Tree) (processed queries : ℕ) :
    (run C read fuel s t processed queries).cursor =
      advance read (build C t (readKeys read fuel s)).processed s := by
  induction fuel generalizing s t processed queries with
  | zero => rfl
  | succ fuel ih =>
    cases hr : read s with
    | none => simp [run, readKeys, hr, build, advance]
    | some pair =>
      obtain ⟨key, next⟩ := pair
      simp only [run, readKeys, hr, build]
      split
      · simpa only [tick, advance, hr] using ih next t (processed + 1) (queries + 1)
      · split
        · simp [advance, hr]
        · simpa only [tick, advance, hr] using
            ih next (insert t key) (processed + 1) (queries + 1)

theorem readKeys_eq_take {σ : Type u} (read : σ → Option (List Bool × σ))
    (view : σ → List (List Bool)) (hread : RowMerge.IsReader read view)
    (fuel : ℕ) (s : σ) : readKeys read fuel s = (view s).take fuel := by
  induction fuel generalizing s with
  | zero => simp [readKeys]
  | succ fuel ih =>
    have hv := hread s
    cases hr : read s with
    | none =>
      simp only [hr] at hv
      simp [readKeys, hr, hv]
    | some pair =>
      obtain ⟨key, next⟩ := pair
      simp only [hr] at hv
      simp [readKeys, hr, hv, ih]

theorem advance_view {σ : Type u} (read : σ → Option (List Bool × σ))
    (view : σ → List (List Bool)) (hread : RowMerge.IsReader read view)
    (count : ℕ) (s : σ) : view (advance read count s) = (view s).drop count := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih =>
    have hv := hread s
    cases hr : read s with
    | none =>
      simp only [hr] at hv
      simp [advance, hr, hv]
    | some pair =>
      obtain ⟨key, next⟩ := pair
      simp only [hr] at hv
      simp [advance, hr, hv, ih]

/-- The actual cursor loop completes and retains exactly the streamed keys
when they lie in a fixed-width universe whose cardinality fits the cap. -/
theorem run_complete {σ : Type u} {C width fuel : ℕ}
    (read : σ → Option (List Bool × σ)) (view : σ → List (List Bool))
    (hread : RowMerge.IsReader read view) (s : σ) {U : Finset (List Bool)}
    (hfuel : (view s).length ≤ fuel)
    (hwidth : ∀ key ∈ U, key.length = width)
    (hkeys : ∀ key ∈ view s, key ∈ U) (hcap : U.card ≤ C) :
    let r := run C read fuel s .empty 0 0
    r.overflow = false ∧ r.processed = (view s).length ∧
      ∀ query, query.length = width →
        (contains r.tree query = true ↔ query ∈ view s) := by
  have htrace : readKeys read fuel s = view s := by
    rw [readKeys_eq_take read view hread, List.take_of_length_le hfuel]
  have hfit : (build C .empty (view s)).overflow = false :=
    build_fits_universe (by trivial) hwidth (by simp [keySet]) hkeys hcap
  obtain ⟨ht, ho, hp⟩ := run_spec C read fuel s .empty 0 0
  rw [htrace] at ht ho hp
  refine ⟨ho.trans hfit, ?_, ?_⟩
  · simpa only [Nat.zero_add] using hp.trans (by
      simpa only [Nat.zero_add] using build_complete_processed hfit)
  · intro query hq
    rw [ht, build_complete_contains_iff (by trivial)
      (fun key hk => hwidth key (hkeys key hk)) hfit hq]
    simp [contains]

theorem run_complete_distinct {σ : Type u} {C width fuel : ℕ}
    (read : σ → Option (List Bool × σ)) (view : σ → List (List Bool))
    (hread : RowMerge.IsReader read view) (s : σ)
    (hfuel : (view s).length ≤ fuel)
    (hwidth : ∀ key ∈ view s, key.length = width)
    (hcap : (view s).toFinset.card ≤ C) :
    let r := run C read fuel s .empty 0 0
    r.overflow = false ∧ r.processed = (view s).length ∧
      ∀ query, query.length = width →
        (contains r.tree query = true ↔ query ∈ view s) :=
  run_complete read view hread s hfuel
    (fun key hk => hwidth key (List.mem_toFinset.mp hk))
    (fun _ hk => List.mem_toFinset.mpr hk) hcap

theorem run_complete_exhausts {σ : Type u} {C width fuel : ℕ}
    (read : σ → Option (List Bool × σ)) (view : σ → List (List Bool))
    (hread : RowMerge.IsReader read view) (s : σ)
    (hfuel : (view s).length ≤ fuel)
    (hwidth : ∀ key ∈ view s, key.length = width)
    (hcap : (view s).toFinset.card ≤ C) :
    view (run C read fuel s .empty 0 0).cursor = [] := by
  have htrace : readKeys read fuel s = view s := by
    rw [readKeys_eq_take read view hread, List.take_of_length_le hfuel]
  have hfit : (build C .empty (view s)).overflow = false :=
    build_fits_universe (by trivial)
      (fun key hk => hwidth key (List.mem_toFinset.mp hk))
      (by simp [keySet]) (fun _ hk => List.mem_toFinset.mpr hk) hcap
  rw [run_cursor, htrace, build_complete_processed hfit, advance_view read view hread,
    List.drop_length]

theorem run_complete_from_values {σ : Type u} {α : Type*} [DecidableEq α]
    {C width fuel : ℕ} (read : σ → Option (List Bool × σ))
    (view : σ → List (List Bool)) (hread : RowMerge.IsReader read view) (s : σ)
    (X : Finset α) (encode : α → List Bool) (hfuel : (view s).length ≤ fuel)
    (hwidth : ∀ x ∈ X, (encode x).length = width)
    (hkeys : ∀ key ∈ view s, ∃ x ∈ X, encode x = key) (hcap : X.card ≤ C) :
    let r := run C read fuel s .empty 0 0
    r.overflow = false ∧ r.processed = (view s).length ∧
      ∀ query, query.length = width →
        (contains r.tree query = true ↔ query ∈ view s) := by
  apply run_complete read view hread s hfuel (U := X.image encode)
  · intro key hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact hwidth x hx
  · intro key hk
    obtain ⟨x, hx, rfl⟩ := hkeys key hk
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · exact (Finset.card_image_le).trans hcap

end LowSpaceSubsetSum.BinaryTrie

end OAI
