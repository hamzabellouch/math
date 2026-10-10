import OAI.Combinatorics.LowSpaceSubsetSum.Streams.RecordedDictionary

namespace OAI

/-! # Exact retained-record semantics for a filtered stream join -/

namespace LowSpaceSubsetSum.RecordedDictionary

variable {α β γ : Type*}

/-- A proof view; the runtime never constructs this Cartesian list. -/
def matchingRecords (key₁ : β → ℤ) (key₂ : γ → ℤ) (emit : β → γ → Option α)
    (xs : List β) (ys : List γ) : List α :=
  xs.flatMap (fun x => (ys.filter (fun y => decide (key₁ x = key₂ y))).filterMap (emit x))

theorem mem_matchingRecords (key₁ : β → ℤ) (key₂ : γ → ℤ) (emit : β → γ → Option α)
    (xs : List β) (ys : List γ) (z : α) :
    z ∈ matchingRecords key₁ key₂ emit xs ys ↔
      ∃ x ∈ xs, ∃ y ∈ ys, key₁ x = key₂ y ∧ emit x y = some z := by
  simp only [matchingRecords, List.mem_flatMap, List.mem_filterMap, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx, y, ⟨hy, he⟩, hz⟩
    exact ⟨x, hx, y, hy, he, hz⟩
  · rintro ⟨x, hx, y, hy, he, hz⟩
    exact ⟨x, hx, y, ⟨hy, he⟩, hz⟩

theorem matchFold_eq_records (C : ℕ) (encode : α → List Bool)
    (key₁ : β → ℤ) (key₂ : γ → ℤ) (emit : β → γ → Option α)
    (xs : List β) (ys : List γ) (r : State α) :
    MatchFold.run key₁ key₂ (callback C encode emit) xs ys r =
      (matchingRecords key₁ key₂ emit xs ys).foldl (fun r z => feed C encode z r) r := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih =>
    simp only [MatchFold.run, matchingRecords, List.flatMap_cons, List.foldl_append,
      List.foldl_filterMap, callback, ih]
    congr 2
    funext a y
    cases emit x y <;> rfl

theorem fold_provenance (C : ℕ) (encode : α → List Bool) (xs : List α) (r : State α)
    (P : α → Prop) (hr : ∀ z ∈ r.records.toList, P z) (hx : ∀ z ∈ xs, P z) :
    ∀ z ∈ (xs.foldl (fun r z => feed C encode z r) r).records.toList, P z := by
  induction xs generalizing r with
  | nil => exact hr
  | cons x xs ih =>
    exact ih (feed C encode x r) (feed_provenance C encode x r P hr (hx x (by simp)))
      (fun y hy => hx y (by simp [hy]))

theorem matchFold_fits {C width : ℕ} (encode : α → List Bool)
    (key₁ : β → ℤ) (key₂ : γ → ℤ) (emit : β → γ → Option α)
    (xs : List β) (ys : List γ) (U : Finset (List Bool))
    (hwidth : ∀ q ∈ U, q.length = width) (hcap : U.card ≤ C)
    (hkeys : ∀ x ∈ xs, ∀ y ∈ ys, key₁ x = key₂ y →
      ∀ z, emit x y = some z → encode z ∈ U) :
    let r := MatchFold.run key₁ key₂ (callback C encode emit) xs ys empty
    r.keys.overflow = false ∧ ∀ q,
      (∃ z ∈ r.records.toList, encode z = q) ↔
        ∃ x ∈ xs, ∃ y ∈ ys, key₁ x = key₂ y ∧
          ∃ z, emit x y = some z ∧ encode z = q := by
  rw [matchFold_eq_records]
  have hf := fold_fits (width := width) encode (matchingRecords key₁ key₂ emit xs ys)
    U hwidth hcap (by
      intro z hz
      obtain ⟨x, hx, y, hy, he, hz⟩ := (mem_matchingRecords _ _ _ _ _ _).mp hz
      exact hkeys x hx y hy he z hz)
  refine ⟨hf.1, ?_⟩
  intro q
  rw [hf.2]
  constructor
  · rintro ⟨z, hz, he⟩
    obtain ⟨x, hx, y, hy, hm, hz⟩ := (mem_matchingRecords _ _ _ _ _ _).mp hz
    exact ⟨x, hx, y, hy, hm, z, hz, he⟩
  · rintro ⟨x, hx, y, hy, hm, z, hz, he⟩
    exact ⟨z, (mem_matchingRecords _ _ _ _ _ _).mpr ⟨x, hx, y, hy, hm, hz⟩, he⟩

theorem join_eq_records {σ₁ σ₂ : Type*} (C : ℕ) (encode : α → List Bool)
    (read₁ : σ₁ → Option (β × σ₁)) (key₁ : β → ℤ)
    (read₂ : σ₂ → Option (γ × σ₂)) (key₂ : γ → ℤ) (emit : β → γ → Option α)
    (view₁ : σ₁ → List β) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List γ) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ controlFuel : ℕ) (s₁ : σ₁) (s₂ : σ₂) (r : State α)
    (hsort₁ : (view₁ s₁).Pairwise (fun x y => key₁ x ≤ key₁ y))
    (hsort₂ : (view₂ s₂).Pairwise (fun x y => key₂ x ≤ key₂ y))
    (hcap₁ : (view₁ s₁).length ≤ fuel₁) (hcap₂ : (view₂ s₂).length ≤ fuel₂)
    (hfuel : (view₁ s₁).length + (view₂ s₂).length < controlFuel) :
    (StreamJoin.stopped read₁ key₁ read₂ key₂ (callback C encode emit)
      B fuel₁ fuel₂ controlFuel s₁ s₂ r).state.user =
        (matchingRecords key₁ key₂ emit (view₁ s₁) (view₂ s₂)).foldl
          (fun r z => feed C encode z r) r := by
  rw [StreamJoin.stopped_eq, StreamJoin.run_complete read₁ key₁ read₂ key₂
    (callback C encode emit) (fun _ _ _ => rfl) view₁ hread₁ view₂ hread₂ B fuel₁ fuel₂
    controlFuel s₁ s₂ r hsort₁ hsort₂ hcap₁ hcap₂ hfuel, matchFold_eq_records]

/-- No capacity hypothesis is needed for provenance: overflowing joins retain
only entries emitted by a matching pair. -/
theorem join_provenance {σ₁ σ₂ : Type*} (C : ℕ) (encode : α → List Bool)
    (read₁ : σ₁ → Option (β × σ₁)) (key₁ : β → ℤ)
    (read₂ : σ₂ → Option (γ × σ₂)) (key₂ : γ → ℤ) (emit : β → γ → Option α)
    (view₁ : σ₁ → List β) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List γ) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ controlFuel : ℕ) (s₁ : σ₁) (s₂ : σ₂)
    (hsort₁ : (view₁ s₁).Pairwise (fun x y => key₁ x ≤ key₁ y))
    (hsort₂ : (view₂ s₂).Pairwise (fun x y => key₂ x ≤ key₂ y))
    (hcap₁ : (view₁ s₁).length ≤ fuel₁) (hcap₂ : (view₂ s₂).length ≤ fuel₂)
    (hfuel : (view₁ s₁).length + (view₂ s₂).length < controlFuel)
    (z : α) (hz : z ∈ (StreamJoin.stopped read₁ key₁ read₂ key₂ (callback C encode emit)
      B fuel₁ fuel₂ controlFuel s₁ s₂ empty).state.user.records.toList) :
    ∃ x ∈ view₁ s₁, ∃ y ∈ view₂ s₂, key₁ x = key₂ y ∧ emit x y = some z := by
  rw [join_eq_records C encode read₁ key₁ read₂ key₂ emit view₁ hread₁ view₂ hread₂
    B fuel₁ fuel₂ controlFuel s₁ s₂ empty hsort₁ hsort₂ hcap₁ hcap₂ hfuel] at hz
  exact (mem_matchingRecords key₁ key₂ emit _ _ z).mp
    (fold_provenance C encode (matchingRecords key₁ key₂ emit (view₁ s₁) (view₂ s₂))
      empty (fun z => z ∈ matchingRecords key₁ key₂ emit (view₁ s₁) (view₂ s₂))
      (by simp [empty]) (fun _ h => h) z hz)

end LowSpaceSubsetSum.RecordedDictionary

end OAI
