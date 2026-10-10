import OAI.Combinatorics.LowSpaceSubsetSum.Streams.DictionaryStream
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.StreamJoinCorrectness

namespace OAI

/-!
# A bounded dictionary callback for the actual stream join

The callback freezes after the first capacity violation. It always lets the
join continue, so the established complete-join theorem applies on every
outcome. The overflowing residue is discarded afterwards. Completing the
scan uses only the bounded Cartesian potential and no extra keys.
-/

namespace LowSpaceSubsetSum.BinaryTrie

def feed (C : ℕ) (key : List Bool) (r : BuildResult) : BuildResult :=
  if r.overflow then r
  else if contains r.tree key then tick r
  else
    let next := insert r.tree key
    ⟨next, decide (C < entries next), r.processed + 1⟩

def callback {α β : Type*} (C : ℕ) (encode : α → β → List Bool)
    (x : α) (y : β) (r : BuildResult) : BuildResult × Bool :=
  (feed C (encode x y) r, false)

theorem feed_frozen (C : ℕ) (key : List Bool) (r : BuildResult)
    (h : r.overflow = true) : feed C key r = r := by simp [feed, h]

structure Safe (C width : ℕ) (r : BuildResult) : Prop where
  hasWidth : HasWidth r.tree width
  compact : Compact r.tree
  bound : entries r.tree ≤ C + 1
  complete_bound : r.overflow = false → entries r.tree ≤ C

theorem empty_safe (C width : ℕ) : Safe C width ⟨.empty, false, 0⟩ := by
  constructor <;> simp [HasWidth, Compact, entries]

theorem feed_safe {C width : ℕ} {r : BuildResult} (hr : Safe C width r)
    (key : List Bool) (hk : key.length = width) : Safe C width (feed C key r) := by
  by_cases hover : r.overflow = true
  · simpa only [feed_frozen C key r hover] using hr
  have hclear : r.overflow = false := Bool.eq_false_iff.mpr hover
  by_cases hdup : contains r.tree key = true
  · simp only [feed, hclear, Bool.false_eq_true, ↓reduceIte, hdup, tick]
    exact ⟨hr.hasWidth, hr.compact, hr.bound, fun _ => hr.complete_bound hclear⟩
  have hnew : contains r.tree key = false := Bool.eq_false_iff.mpr hdup
  have he := entries_insert hr.hasWidth hk
  rw [hnew] at he
  simp only [Bool.false_eq_true, ↓reduceIte] at he
  have hcap := hr.complete_bound hclear
  simp only [feed, hclear, hnew, Bool.false_eq_true, ↓reduceIte]
  refine ⟨insert_hasWidth hr.hasWidth hk, insert_compact hr.compact key, ?_, ?_⟩
  · dsimp
    omega
  · intro h
    have hh : ¬ C < entries (insert r.tree key) := of_decide_eq_false h
    change entries (insert r.tree key) ≤ C
    omega

theorem feed_nodes {C width : ℕ} {r : BuildResult} (hr : Safe C width r)
    (key : List Bool) (hk : key.length = width) :
    nodes (feed C key r).tree ≤ (width + 1) * (C + 1) := by
  have h := feed_safe hr key hk
  exact (nodes_le_width_mul_entries h.hasWidth h.compact).trans
    (Nat.mul_le_mul_left _ h.bound)

/-- The cardinality hypothesis is on the actual possible key set, not the
number of callbacks. Duplicate occurrences never consume extra capacity. -/
theorem feed_fits {C width : ℕ} {r : BuildResult} {U : Finset (List Bool)}
    (hclear : r.overflow = false) (ht : HasWidth r.tree width)
    (hwidth : ∀ key ∈ U, key.length = width) (htU : keySet r.tree ⊆ U)
    (hcap : U.card ≤ C) {key : List Bool} (hkey : key ∈ U) :
    (feed C key r).overflow = false ∧
      keySet (feed C key r).tree = Insert.insert key (keySet r.tree) ∧
      (feed C key r).processed = r.processed + 1 ∧
      HasWidth (feed C key r).tree width := by
  have hk := hwidth key hkey
  by_cases hdup : contains r.tree key = true
  · have hm : key ∈ keySet r.tree := (mem_keySet _ _).mpr hdup
    simp only [feed, hclear, Bool.false_eq_true, ↓reduceIte, hdup, tick]
    exact ⟨trivial, (Finset.insert_eq_of_mem hm).symm, trivial, ht⟩
  · have hnew : contains r.tree key = false := Bool.eq_false_iff.mpr hdup
    have hnextU : keySet (insert r.tree key) ⊆ U := by
      rw [keySet_insert ht hk]
      exact Finset.insert_subset hkey htU
    have hnext : entries (insert r.tree key) ≤ C := by
      rw [← card_keySet]
      exact (Finset.card_le_card hnextU).trans hcap
    simp only [feed, hclear, hnew, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by simp [show ¬ C < entries (insert r.tree key) by omega],
      keySet_insert ht hk, trivial, insert_hasWidth ht hk⟩

theorem fold_fits {C width : ℕ} {r : BuildResult} {U : Finset (List Bool)}
    (hclear : r.overflow = false) (ht : HasWidth r.tree width)
    (hwidth : ∀ key ∈ U, key.length = width) (htU : keySet r.tree ⊆ U)
    (hcap : U.card ≤ C) (keys : List (List Bool)) (hkeys : ∀ key ∈ keys, key ∈ U) :
    let out := keys.foldl (fun r key => feed C key r) r
    out.overflow = false ∧ keySet out.tree = keySet r.tree ∪ keys.toFinset ∧
      out.processed = r.processed + keys.length ∧ HasWidth out.tree width := by
  induction keys generalizing r with
  | nil => simp [ht, hclear]
  | cons key rest ih =>
    obtain ⟨hc, hs, hp, hw⟩ := feed_fits hclear ht hwidth htU hcap (hkeys key (by simp))
    have hnU : keySet (feed C key r).tree ⊆ U := by
      rw [hs]
      exact Finset.insert_subset (hkeys key (by simp)) htU
    obtain ⟨hfin, hset, hnum, hwidthFin⟩ := ih hc hw hnU
      (fun q hq => hkeys q (by simp [hq]))
    refine ⟨hfin, ?_, ?_, hwidthFin⟩
    · change keySet (rest.foldl (fun r key => feed C key r) (feed C key r)).tree = _
      rw [hset, hs, List.toFinset_cons]
      ext q
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    · change (rest.foldl (fun r key => feed C key r) (feed C key r)).processed = _
      rw [hnum, hp, List.length_cons]
      omega

theorem fold_safe {C width : ℕ} {r : BuildResult} (hr : Safe C width r)
    (keys : List (List Bool)) (hk : ∀ key ∈ keys, key.length = width) :
    Safe C width (keys.foldl (fun r key => feed C key r) r) := by
  induction keys generalizing r with
  | nil => exact hr
  | cons key rest ih =>
    exact ih (feed_safe hr key (hk key (by simp))) (fun q hq => hk q (by simp [hq]))

/-- Proof-only list of keys reported by a complete Cartesian-match join. -/
def matchingKeys {α β : Type*} (key₁ : α → ℤ) (key₂ : β → ℤ)
    (encode : α → β → List Bool) (xs : List α) (ys : List β) : List (List Bool) :=
  xs.flatMap (fun x => (ys.filter (fun y => decide (key₁ x = key₂ y))).map (encode x))

theorem mem_matchingKeys {α β : Type*} (key₁ : α → ℤ) (key₂ : β → ℤ)
    (encode : α → β → List Bool) (xs : List α) (ys : List β) (key : List Bool) :
    key ∈ matchingKeys key₁ key₂ encode xs ys ↔
      ∃ x ∈ xs, ∃ y ∈ ys, key₁ x = key₂ y ∧ encode x y = key := by
  simp [matchingKeys, and_assoc]

theorem matchFold_eq_keys {α β : Type*} (C : ℕ) (key₁ : α → ℤ) (key₂ : β → ℤ)
    (encode : α → β → List Bool) (xs : List α) (ys : List β) (r : BuildResult) :
    MatchFold.run key₁ key₂ (callback C encode) xs ys r =
      (matchingKeys key₁ key₂ encode xs ys).foldl (fun r key => feed C key r) r := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih =>
    simp only [MatchFold.run, matchingKeys, List.flatMap_cons, List.foldl_append,
      List.foldl_map, callback, ih]

theorem matchFold_fits {α β : Type*} {C width : ℕ} (key₁ : α → ℤ) (key₂ : β → ℤ)
    (encode : α → β → List Bool) (xs : List α) (ys : List β) (U : Finset (List Bool))
    (hwidth : ∀ key ∈ U, key.length = width) (hcap : U.card ≤ C)
    (hkeys : ∀ x ∈ xs, ∀ y ∈ ys, key₁ x = key₂ y → encode x y ∈ U) :
    let out := MatchFold.run key₁ key₂ (callback C encode) xs ys ⟨.empty, false, 0⟩
    out.overflow = false ∧
      keySet out.tree = (matchingKeys key₁ key₂ encode xs ys).toFinset ∧
      out.processed = (matchingKeys key₁ key₂ encode xs ys).length := by
  rw [matchFold_eq_keys]
  have h := fold_fits (r := ⟨.empty, false, 0⟩) rfl (by trivial) hwidth
    (by simp [keySet]) hcap (matchingKeys key₁ key₂ encode xs ys) (by
      intro key hk
      obtain ⟨x, hx, y, hy, heq, rfl⟩ := (mem_matchingKeys _ _ _ _ _ _).mp hk
      exact hkeys x hx y hy heq)
  refine ⟨h.1, ?_, ?_⟩
  · simpa only [keySet, Finset.empty_union] using h.2.1
  · simpa only [Nat.zero_add] using h.2.2.1

theorem matchFold_safe {α β : Type*} {C width : ℕ} (key₁ : α → ℤ) (key₂ : β → ℤ)
    (encode : α → β → List Bool) (xs : List α) (ys : List β)
    (hwidth : ∀ x ∈ xs, ∀ y ∈ ys, key₁ x = key₂ y → (encode x y).length = width) :
    Safe C width (MatchFold.run key₁ key₂ (callback C encode) xs ys ⟨.empty, false, 0⟩) := by
  rw [matchFold_eq_keys]
  apply fold_safe (empty_safe C width)
  intro key hk
  obtain ⟨x, hx, y, hy, heq, rfl⟩ := (mem_matchingKeys _ _ _ _ _ _).mp hk
  exact hwidth x hx y hy heq

/-- Exact membership after the actual finite-state stream join. The only
capacity assumption is the cardinality of a universe containing its keys. -/
theorem join_fits {α β σ₁ σ₂ : Type*} {C width : ℕ}
    (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (encode : α → β → List Bool)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ controlFuel : ℕ) (s₁ : σ₁) (s₂ : σ₂)
    (hsort₁ : (view₁ s₁).Pairwise (fun x y => key₁ x ≤ key₁ y))
    (hsort₂ : (view₂ s₂).Pairwise (fun x y => key₂ x ≤ key₂ y))
    (hcap₁ : (view₁ s₁).length ≤ fuel₁) (hcap₂ : (view₂ s₂).length ≤ fuel₂)
    (hfuel : (view₁ s₁).length + (view₂ s₂).length < controlFuel)
    (U : Finset (List Bool)) (hwidth : ∀ key ∈ U, key.length = width) (hcap : U.card ≤ C)
    (hkeys : ∀ x ∈ view₁ s₁, ∀ y ∈ view₂ s₂, key₁ x = key₂ y → encode x y ∈ U) :
    let out := (StreamJoin.run read₁ key₁ read₂ key₂ (callback C encode)
      B fuel₁ fuel₂ controlFuel s₁ s₂ ⟨.empty, false, 0⟩).user
    out.overflow = false ∧ ∀ query,
      contains out.tree query = true ↔
        ∃ x ∈ view₁ s₁, ∃ y ∈ view₂ s₂, key₁ x = key₂ y ∧ encode x y = query := by
  have he := StreamJoin.run_complete read₁ key₁ read₂ key₂ (callback C encode)
    (fun _ _ _ => rfl) view₁ hread₁ view₂ hread₂ B fuel₁ fuel₂ controlFuel
    s₁ s₂ ⟨.empty, false, 0⟩ hsort₁ hsort₂ hcap₁ hcap₂ hfuel
  dsimp only
  rw [he]
  obtain ⟨hc, hs, _⟩ := matchFold_fits key₁ key₂ encode (view₁ s₁) (view₂ s₂)
    U hwidth hcap hkeys
  refine ⟨hc, ?_⟩
  intro query
  rw [← mem_keySet, hs, List.mem_toFinset, mem_matchingKeys]

/-- Every complete join, including an overflowing residue, retains at most
one rejected key beyond capacity. This gives the concrete trie node bound. -/
theorem join_nodes {α β σ₁ σ₂ : Type*} {C width : ℕ}
    (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (encode : α → β → List Bool)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ controlFuel : ℕ) (s₁ : σ₁) (s₂ : σ₂)
    (hsort₁ : (view₁ s₁).Pairwise (fun x y => key₁ x ≤ key₁ y))
    (hsort₂ : (view₂ s₂).Pairwise (fun x y => key₂ x ≤ key₂ y))
    (hcap₁ : (view₁ s₁).length ≤ fuel₁) (hcap₂ : (view₂ s₂).length ≤ fuel₂)
    (hfuel : (view₁ s₁).length + (view₂ s₂).length < controlFuel)
    (hwidth : ∀ x ∈ view₁ s₁, ∀ y ∈ view₂ s₂,
      key₁ x = key₂ y → (encode x y).length = width) :
    nodes (StreamJoin.run read₁ key₁ read₂ key₂ (callback C encode)
      B fuel₁ fuel₂ controlFuel s₁ s₂ ⟨.empty, false, 0⟩).user.tree ≤
      (width + 1) * (C + 1) := by
  rw [StreamJoin.run_complete read₁ key₁ read₂ key₂ (callback C encode)
    (fun _ _ _ => rfl) view₁ hread₁ view₂ hread₂ B fuel₁ fuel₂ controlFuel
    s₁ s₂ ⟨.empty, false, 0⟩ hsort₁ hsort₂ hcap₁ hcap₂ hfuel]
  have h := matchFold_safe (C := C) key₁ key₂ encode (view₁ s₁) (view₂ s₂) hwidth
  exact (nodes_le_width_mul_entries h.hasWidth h.compact).trans
    (Nat.mul_le_mul_left _ h.bound)

end LowSpaceSubsetSum.BinaryTrie

end OAI
