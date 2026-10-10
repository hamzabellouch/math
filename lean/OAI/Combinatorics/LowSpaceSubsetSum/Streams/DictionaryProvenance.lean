import OAI.Combinatorics.LowSpaceSubsetSum.Streams.DictionaryCallback

namespace OAI

/-!
# Provenance of every retained bounded-dictionary key

Capacity failure can freeze a callback, but cannot create an unreported key.
The proof applies even to overflowing complete joins, with no cardinality
hypothesis on a bucket and no knowledge of any solution.
-/

namespace LowSpaceSubsetSum.BinaryTrie

theorem feed_provenance {width : ℕ} (C : ℕ) (r : BuildResult)
    (hr : HasWidth r.tree width) (key : List Bool) (hk : key.length = width) :
    HasWidth (feed C key r).tree width ∧
      keySet (feed C key r).tree ⊆ Insert.insert key (keySet r.tree) := by
  by_cases ho : r.overflow = true
  · rw [feed_frozen C key r ho]
    exact ⟨hr, Finset.subset_insert _ _⟩
  have hc : r.overflow = false := Bool.eq_false_iff.mpr ho
  by_cases hd : contains r.tree key = true
  · simp only [feed, hc, hd, Bool.false_eq_true, ↓reduceIte, tick]
    exact ⟨hr, Finset.subset_insert _ _⟩
  have hf : contains r.tree key = false := Bool.eq_false_iff.mpr hd
  simp only [feed, hc, hf, Bool.false_eq_true, ↓reduceIte]
  exact ⟨insert_hasWidth hr hk, by rw [keySet_insert hr hk]⟩

theorem fold_provenance {width : ℕ} (C : ℕ) (keys : List (List Bool)) (r : BuildResult)
    (hr : HasWidth r.tree width) (hk : ∀ key ∈ keys, key.length = width) :
    keySet (keys.foldl (fun r key => feed C key r) r).tree ⊆ keySet r.tree ∪ keys.toFinset := by
  induction keys generalizing r with
  | nil => simp
  | cons key keys ih =>
    have hf := feed_provenance C r hr key (hk key (by simp))
    have hi := ih (feed C key r) hf.1 (fun q hq => hk q (by simp [hq]))
    intro q hq
    rcases Finset.mem_union.mp (hi hq) with h | h
    · rcases Finset.mem_insert.mp (hf.2 h) with rfl | h
      · simp
      · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (by simp [h])

theorem matchFold_provenance {α β : Type*} {C width : ℕ}
    (key₁ : α → ℤ) (key₂ : β → ℤ) (encode : α → β → List Bool)
    (xs : List α) (ys : List β)
    (hwidth : ∀ x ∈ xs, ∀ y ∈ ys, key₁ x = key₂ y → (encode x y).length = width)
    (query : List Bool)
    (hq : contains (MatchFold.run key₁ key₂ (callback C encode) xs ys
      ⟨.empty, false, 0⟩).tree query = true) :
    ∃ x ∈ xs, ∃ y ∈ ys, key₁ x = key₂ y ∧ encode x y = query := by
  rw [matchFold_eq_keys] at hq
  have hp := fold_provenance C (matchingKeys key₁ key₂ encode xs ys) ⟨.empty, false, 0⟩
    (width := width) (by trivial) (by
      intro key hk
      obtain ⟨x, hx, y, hy, he, rfl⟩ := (mem_matchingKeys _ _ _ _ _ _).mp hk
      exact hwidth x hx y hy he)
  have hm := hp ((mem_keySet _ _).mpr hq)
  simp only [keySet, Finset.empty_union, List.mem_toFinset] at hm
  exact (mem_matchingKeys _ _ _ _ _ _).mp hm

theorem join_provenance {α β σ₁ σ₂ : Type*} {C width : ℕ}
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
      key₁ x = key₂ y → (encode x y).length = width)
    (query : List Bool)
    (hq : contains (StreamJoin.run read₁ key₁ read₂ key₂ (callback C encode)
      B fuel₁ fuel₂ controlFuel s₁ s₂ ⟨.empty, false, 0⟩).user.tree query = true) :
    ∃ x ∈ view₁ s₁, ∃ y ∈ view₂ s₂, key₁ x = key₂ y ∧ encode x y = query := by
  rw [StreamJoin.run_complete read₁ key₁ read₂ key₂ (callback C encode)
    (fun _ _ _ => rfl) view₁ hread₁ view₂ hread₂ B fuel₁ fuel₂ controlFuel
    s₁ s₂ ⟨.empty, false, 0⟩ hsort₁ hsort₂ hcap₁ hcap₂ hfuel] at hq
  exact matchFold_provenance key₁ key₂ encode _ _ hwidth query hq

end LowSpaceSubsetSum.BinaryTrie

end OAI
