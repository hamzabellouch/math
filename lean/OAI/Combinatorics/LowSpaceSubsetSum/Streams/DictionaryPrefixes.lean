import OAI.Combinatorics.LowSpaceSubsetSum.Streams.DictionaryCallback

namespace OAI

/-!
# Dictionary space at every stopped join prefix

The callback invariant is preserved inside buffer replay, suffix replay,
tie-group replay, and the outer join loop. Thus the storage bound holds at
every watchdog cutoff, without assuming that a join completes.
-/

namespace LowSpaceSubsetSum.DictionaryPrefixes

theorem one_preserves {α σ τ : Type*}
    (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (P : τ → Prop)
    (hstep : ∀ x a, P a → P (report x a).1)
    (buffer : Array α) (saved : σ) (long : Bool) (fuel : ℕ) (a : τ) (ha : P a) :
    P (JoinOne.run read key K report buffer saved long fuel a).state := by
  have hb : P (BufferReplay.run key K report buffer a).state := by
    exact TieReplay.run_preserves (BufferReplay.read buffer) key K report
      (fun a _ => P a) (fun x a _ ha => hstep x a ha) buffer.size 0 a ha
  dsimp only [JoinOne.run]
  split
  · exact hb
  · split
    · exact TieReplay.run_preserves read key K report (fun a _ => P a)
        (fun x a _ ha => hstep x a ha) fuel saved _ hb
    · exact hb

theorem group_preserves {α β σ₁ σ₂ τ : Type*}
    (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (K : ℤ)
    (report : α → β → τ → τ × Bool) (P : τ → Prop)
    (hstep : ∀ x y a, P a → P (report x y a).1)
    (B fuel₁ fuel₂ : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ) (ha : P a) :
    P (TieGroup.run read₁ key₁ read₂ key₂ K report B fuel₁ fuel₂ s₁ s₂ a).outer.state.user := by
  let filled := TieBuffer.fill read₂ key₂ K B s₂
  let long := TieBuffer.hasKey read₂ key₂ K filled.cursor
  have hs : ∀ x (st : TieGroup.State σ₂ τ) (_r : ℕ), P st.user →
      P (TieGroup.step read₂ key₂ K report filled.buffer filled.cursor long fuel₂ x st).1.user := by
    intro x st _ hst
    exact one_preserves read₂ key₂ K (report x) P (hstep x)
      filled.buffer filled.cursor long fuel₂ st.user hst
  exact TieReplay.run_preserves read₁ key₁ K
    (TieGroup.step read₂ key₂ K report filled.buffer filled.cursor long fuel₂)
    (fun st _ => P st.user) hs fuel₁ s₁ ⟨filled.cursor, a, 0, 0, 0⟩ ha

theorem step_preserves {α β σ₁ σ₂ τ : Type*}
    (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (P : τ → Prop)
    (hstep : ∀ x y a, P a → P (report x y a).1)
    (B fuel₁ fuel₂ : ℕ) (st : StreamJoin.State σ₁ σ₂ τ) (ha : P st.user) :
    P (StreamJoin.step read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ st).user := by
  by_cases hd : st.done = true
  · simpa only [StreamJoin.step_done _ _ _ _ _ _ _ _ st hd] using ha
  have hdf : st.done = false := Bool.eq_false_iff.mpr hd
  cases hx : read₁ st.left with
  | none => simpa only [StreamJoin.step, hdf, Bool.false_eq_true, ↓reduceIte, hx] using ha
  | some xp =>
    obtain ⟨x, left'⟩ := xp
    cases hy : read₂ st.right with
    | none =>
      simpa only [StreamJoin.step, hdf, Bool.false_eq_true, ↓reduceIte, hx, hy] using ha
    | some yp =>
      obtain ⟨y, right'⟩ := yp
      simp only [StreamJoin.step, hdf, Bool.false_eq_true, ↓reduceIte, hx, hy]
      split
      · exact ha
      · split
        · exact ha
        · exact group_preserves read₁ key₁ read₂ key₂ (key₁ x) report P hstep
            B fuel₁ fuel₂ st.left st.right st.user ha

theorem run_preserves {α β σ₁ σ₂ τ : Type*}
    (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (P : τ → Prop)
    (hstep : ∀ x y a, P a → P (report x y a).1)
    (B fuel₁ fuel₂ controlFuel : ℕ) (st : StreamJoin.State σ₁ σ₂ τ) (ha : P st.user) :
    P (StreamJoin.runAcc read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ controlFuel st).user := by
  induction controlFuel generalizing st with
  | zero => exact ha
  | succ fuel ih =>
    exact ih _ (step_preserves read₁ key₁ read₂ key₂ report P hstep B fuel₁ fuel₂ st ha)

/-- No reader law, sortedness, completeness, or probability event is needed
for the dictionary-space invariant at a stopped control prefix. -/
theorem stopped_safe {α β σ₁ σ₂ : Type*} {C width : ℕ}
    (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (encode : α → β → List Bool) (hwidth : ∀ x y, (encode x y).length = width)
    (B fuel₁ fuel₂ controlFuel : ℕ) (s₁ : σ₁) (s₂ : σ₂) :
    BinaryTrie.Safe C width (StreamJoin.run read₁ key₁ read₂ key₂
      (BinaryTrie.callback C encode) B fuel₁ fuel₂ controlFuel s₁ s₂ ⟨.empty, false, 0⟩).user := by
  exact run_preserves read₁ key₁ read₂ key₂ (BinaryTrie.callback C encode)
    (BinaryTrie.Safe C width) (fun x y a ha => BinaryTrie.feed_safe ha _ (hwidth x y))
    B fuel₁ fuel₂ controlFuel (StreamJoin.start s₁ s₂ ⟨.empty, false, 0⟩)
    (BinaryTrie.empty_safe C width)

theorem stopped_nodes {α β σ₁ σ₂ : Type*} {C width : ℕ}
    (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (encode : α → β → List Bool) (hwidth : ∀ x y, (encode x y).length = width)
    (B fuel₁ fuel₂ controlFuel : ℕ) (s₁ : σ₁) (s₂ : σ₂) :
    BinaryTrie.nodes (StreamJoin.run read₁ key₁ read₂ key₂ (BinaryTrie.callback C encode)
      B fuel₁ fuel₂ controlFuel s₁ s₂ ⟨.empty, false, 0⟩).user.tree ≤
      (width + 1) * (C + 1) := by
  have h := stopped_safe (C := C) read₁ key₁ read₂ key₂ encode hwidth
    B fuel₁ fuel₂ controlFuel s₁ s₂
  exact (BinaryTrie.nodes_le_width_mul_entries h.hasWidth h.compact).trans
    (Nat.mul_le_mul_left _ h.bound)

end LowSpaceSubsetSum.DictionaryPrefixes

end OAI
