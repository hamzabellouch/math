import Mathlib.Algebra.Order.Ring.Int

namespace OAI

/-! # The graph update and the regular-row invariant in one transfer -/

namespace Ostmann

/-- The true branch is the positive copy. -/
def transferCopySign (t : Bool) : ℤ := if t then 1 else -1

/-- `none` is the erased pivot; `some (inl h)` is a copied slot and
`some (inr y)` is a shared outside slot. -/
def transferredGraph {H Y : Type*}
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) :
    ((Bool × H) ⊕ Y) → ((Bool × H) ⊕ Y) → ℤ
  | .inl (t, h), .inl (u, k) =>
      if t = u then transferCopySign t * b (some (.inl h)) (some (.inl k))
      else transferCopySign t * b (some (.inl h)) none
  | .inl (t, h), .inr y => transferCopySign t * b (some (.inl h)) (some (.inr y))
  | .inr y, .inl (t, h) => transferCopySign t * b (some (.inr y)) (some (.inl h))
  | .inr _, .inr _ => 0

def RegularGraphRow {I : Type*} (b : I → I → ℤ) (i : I) (ε : ℤ) : Prop :=
  ∀ j, j ≠ i → b i j = ε

theorem transferredGraph_regular {H Y : Type*}
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (h : H) (ε : ℤ)
    (hr : RegularGraphRow b (some (.inl h)) ε) (t : Bool) :
    RegularGraphRow (transferredGraph b) (.inl (t, h)) (transferCopySign t * ε) := by
  intro j hj
  cases j with
  | inl q =>
    rcases q with ⟨u, k⟩
    by_cases htu : t = u
    · subst u
      have hkh : k ≠ h := by
        intro he
        subst k
        exact hj rfl
      simp only [transferredGraph, ite_true]
      rw [hr _ (by simpa only [ne_eq, Option.some.injEq, Sum.inl.injEq] using hkh)]
    · simp only [transferredGraph, htu, ite_false]
      rw [hr _ (by simp)]
  | inr y =>
    simp only [transferredGraph]
    rw [hr _ (by simp)]

theorem transferredGraph_diagonal {H Y : Type*}
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (hb : ∀ i, b i i = 0) :
    ∀ i, transferredGraph b i i = 0 := by
  intro i
  cases i with
  | inl q => simp [transferredGraph, hb]
  | inr y => rfl

/-- A future pivot is retained in one fixed copy. Its incoming column is
still constant on its constituent slots. -/
theorem transferredGraph_common_column {H Y : Type*}
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (K : Set H)
    (hc : ∀ i : Option (H ⊕ Y), (∀ h ∈ K, i ≠ some (.inl h)) →
      ∀ h ∈ K, ∀ k ∈ K, b i (some (.inl h)) = b i (some (.inl k)))
    (t : Bool) (i : (Bool × H) ⊕ Y)
    (hi : ∀ h ∈ K, i ≠ .inl (t, h)) :
    ∀ h ∈ K, ∀ k ∈ K,
      transferredGraph b i (.inl (t, h)) = transferredGraph b i (.inl (t, k)) := by
  intro h hh k hk
  cases i with
  | inl q =>
    rcases q with ⟨u, j⟩
    by_cases hut : u = t
    · subst u
      have hj : ∀ a ∈ K, some (Sum.inl j : H ⊕ Y) ≠ some (.inl a) := by
        intro a ha he
        have he' : j = a := by simpa only [Option.some.injEq, Sum.inl.injEq] using he
        subst a
        exact hi j ha rfl
      simp only [transferredGraph, ite_true]
      rw [hc _ hj h hh k hk]
    · simp only [transferredGraph, hut, ite_false]
  | inr y =>
    simp only [transferredGraph]
    rw [hc _ (by intro a _; simp) h hh k hk]

end Ostmann

end OAI
