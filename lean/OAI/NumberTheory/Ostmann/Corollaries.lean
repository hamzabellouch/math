import OAI.NumberTheory.Ostmann.Result

namespace OAI

/-! Prime-sumset indecomposability and its finite-modification and composite-sum consequences. -/

open scoped Pointwise symmDiff

namespace NumberTheory.Ostmann

theorem main (A B : Set ℕ) (hA : A.Nontrivial) (hB : B.Nontrivial) :
    Set.Infinite ((A + B) ∆ {n : ℕ | Nat.Prime n}) :=
  _root_.OAI.Ostmann.main A B hA hB

theorem finite_modification_indecomposable (S : Set ℕ)
    (hS : (S ∆ {n : ℕ | Nat.Prime n}).Finite)
    (A B : Set ℕ) (hA : A.Nontrivial) (hB : B.Nontrivial) :
    A + B ≠ S := by
  intro h
  exact main A B hA hB (h ▸ hS)

theorem infinite_summands (A B : Set ℕ) (hA : A.Infinite) (hB : B.Infinite) :
    ¬ ((A + B) ∆ {n : ℕ | Nat.Prime n}).Finite :=
  main A B hA.nontrivial hB.nontrivial

theorem infinitely_many_nonprime_sums (A B : Set ℕ)
    (hA : A.Nontrivial) (hB : B.Nontrivial)
    (hcover : ∃ N : ℕ, ∀ p : ℕ, N ≤ p → Nat.Prime p → p ∈ A + B) :
    Set.Infinite ((A + B) \ {n : ℕ | Nat.Prime n}) := by
  obtain ⟨N, hN⟩ := hcover
  have hmissing : ({n : ℕ | Nat.Prime n} \ (A + B)).Finite := by
    apply (Set.finite_Iio N).subset
    intro p hp
    by_contra h
    exact hp.2 (hN p (Nat.le_of_not_gt h) hp.1)
  have hunion := main A B hA hB
  rw [Set.symmDiff_def] at hunion
  intro hfinite
  exact hunion (hfinite.union hmissing)

theorem infinitely_many_composite_sums (A B : Set ℕ)
    (hA : A.Nontrivial) (hB : B.Nontrivial)
    (hcover : ∃ N : ℕ, ∀ p : ℕ, N ≤ p → Nat.Prime p → p ∈ A + B) :
    Set.Infinite {n : ℕ | n ∈ A + B ∧ 1 < n ∧ ¬ Nat.Prime n} := by
  have h := (infinitely_many_nonprime_sums A B hA hB hcover).sdiff
    (Set.finite_Iic 1)
  apply h.mono
  intro n hn
  exact ⟨hn.1.1, Nat.lt_of_not_ge hn.2, hn.1.2⟩

end NumberTheory.Ostmann

end OAI
