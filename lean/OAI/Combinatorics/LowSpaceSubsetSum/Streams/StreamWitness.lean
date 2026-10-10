import OAI.Combinatorics.LowSpaceSubsetSum.Streams.StreamJoinCorrectness

namespace OAI

/-! A concrete Boolean match collector for the finite-state stream join. -/

namespace LowSpaceSubsetSum
namespace StreamWitness

universe u v
variable {α : Type u} {β : Type v}

def remember (hit : α → β → Bool) (x : α) (y : β) (a : Bool) : Bool × Bool :=
  (a || hit x y, false)

theorem foldl_remember (hit : α → β → Bool) (x : α) (ys : List β) (a : Bool) :
    ys.foldl (fun a y => (remember hit x y a).1) a = true ↔
      a = true ∨ ∃ y ∈ ys, hit x y = true := by
  induction ys generalizing a with
  | nil => simp
  | cons y ys ih =>
    rw [List.foldl_cons, ih]
    simp only [remember, Bool.or_eq_true, List.mem_cons]
    aesop

theorem matchFold_iff (key₁ : α → ℤ) (key₂ : β → ℤ) (hit : α → β → Bool)
    (xs : List α) (ys : List β) (a : Bool) :
    MatchFold.run key₁ key₂ (remember hit) xs ys a = true ↔
      a = true ∨ ∃ x ∈ xs, ∃ y ∈ ys, key₁ x = key₂ y ∧ hit x y = true := by
  induction xs generalizing a with
  | nil => simp [MatchFold.run]
  | cons x xs ih =>
    rw [MatchFold.run, ih, foldl_remember]
    simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq]
    aesop

theorem matchFold_true (key₁ : α → ℤ) (key₂ : β → ℤ) (hit : α → β → Bool)
    (xs : List α) (ys : List β) :
    MatchFold.run key₁ key₂ (remember hit) xs ys true = true :=
  (matchFold_iff key₁ key₂ hit xs ys true).mpr (Or.inl rfl)

/-- The actual finite-state join finds exactly the matching occurrences
accepted by its pair predicate. The callback retains one Boolean word. -/
theorem run_iff {σ₁ σ₂ : Type*}
    (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (hit : α → β → Bool)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ controlFuel : ℕ) (s₁ : σ₁) (s₂ : σ₂)
    (hsort₁ : (view₁ s₁).Pairwise (fun x y => key₁ x ≤ key₁ y))
    (hsort₂ : (view₂ s₂).Pairwise (fun x y => key₂ x ≤ key₂ y))
    (hcap₁ : (view₁ s₁).length ≤ fuel₁) (hcap₂ : (view₂ s₂).length ≤ fuel₂)
    (hfuel : (view₁ s₁).length + (view₂ s₂).length < controlFuel) :
    (StreamJoin.run read₁ key₁ read₂ key₂ (remember hit) B fuel₁ fuel₂ controlFuel s₁ s₂ false).user = true ↔
      ∃ x ∈ view₁ s₁, ∃ y ∈ view₂ s₂, key₁ x = key₂ y ∧ hit x y = true := by
  rw [StreamJoin.run_complete read₁ key₁ read₂ key₂ (remember hit) (fun _ _ _ => rfl)
    view₁ hread₁ view₂ hread₂ B fuel₁ fuel₂ controlFuel s₁ s₂ false
    hsort₁ hsort₂ hcap₁ hcap₂ hfuel, matchFold_iff]
  simp

/-- An arbitrary stopped control prefix also has one-sided soundness. -/
theorem stopped_sound {σ₁ σ₂ : Type*}
    (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ) (hit : α → β → Bool)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ controlFuel : ℕ) (s₁ : σ₁) (s₂ : σ₂)
    (hsort₁ : (view₁ s₁).Pairwise (fun x y => key₁ x ≤ key₁ y))
    (hsort₂ : (view₂ s₂).Pairwise (fun x y => key₂ x ≤ key₂ y))
    (hcap₁ : (view₁ s₁).length ≤ fuel₁) (hcap₂ : (view₂ s₂).length ≤ fuel₂)
    (hyes : (StreamJoin.run read₁ key₁ read₂ key₂ (remember hit) B fuel₁ fuel₂
      controlFuel s₁ s₂ false).user = true) :
    ∃ x ∈ view₁ s₁, ∃ y ∈ view₂ s₂, key₁ x = key₂ y ∧ hit x y = true := by
  let out := StreamJoin.run read₁ key₁ read₂ key₂ (remember hit) B fuel₁ fuel₂ controlFuel s₁ s₂ false
  have hs := StreamJoin.runAcc_semantics read₁ key₁ read₂ key₂ (remember hit) (fun _ _ _ => rfl)
    view₁ hread₁ view₂ hread₂ B fuel₁ fuel₂ controlFuel (StreamJoin.start s₁ s₂ false)
    ⟨hsort₁, hsort₂, hcap₁, hcap₂⟩
  change MatchFold.run key₁ key₂ (remember hit) (view₁ out.left) (view₂ out.right) out.user =
    MatchFold.run key₁ key₂ (remember hit) (view₁ s₁) (view₂ s₂) false at hs
  have ht : MatchFold.run key₁ key₂ (remember hit) (view₁ s₁) (view₂ s₂) false = true := by
    rw [← hs, hyes]
    exact matchFold_true key₁ key₂ hit _ _
  exact (matchFold_iff key₁ key₂ hit _ _ false).mp ht |>.resolve_left (by decide)

end StreamWitness
end LowSpaceSubsetSum

end OAI
