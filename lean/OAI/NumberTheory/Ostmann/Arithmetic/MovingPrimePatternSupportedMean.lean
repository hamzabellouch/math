import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimePatternBulkMajorant

namespace OAI

/-! # Signed bulk estimates needed only on the original pattern prior -/

namespace Ostmann
open scoped Classical BigOperators

/-- Invalid role assignments outside the original product law require no
analytic estimate. This retains the original harmonic priors when applying
an estimate proved with their precise prime ranges. -/
theorem movingPrimePattern_signed_bulk_mean_on_support {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ) (hE : 0 ≤ E)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hmass : ∀ j, ∑ a, μ j a = 1) (hnmass : ∀ j, ∑ a, ν j a = 1)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (D : ℝ)
    (hG : ∀ x, productPrior
      (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0 →
      ‖movingPatternBulkMean e ν slot G x‖ ≤ D)
    (seed : TreeLeafIndex n × Fin m → A) :
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern G x *
      movingPatternPrimeFlagProduct e prime n t small (movingPatternBulkLeaves n m slot perm) pattern rep x‖ ≤
      ((4 : ℝ) ^ Fintype.card C * E ^ (4 * n * 2 ^ n - Fintype.card C)) * D := by
  let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
  let minor := fun x => if productPrior law x = 0 then ‖movingPatternBulkMean e ν slot G x‖ else D
  have hminor (x) : ‖movingPatternBulkMean e ν slot G x‖ ≤ minor x := by
    dsimp only [minor]
    split_ifs with h
    · exact le_rfl
    · exact hG x h
  have hlaw (i) : ∑ a, law i a = 1 := by
    dsimp only [law]
    cases e i with
    | inl b => exact hnmass b
    | inr c => exact hmass _
  have hmean : (∑ x, productPrior law x * minor x) = D := by
    calc
      _ = ∑ x, productPrior law x * D := by
        apply Finset.sum_congr rfl
        intro x _
        dsimp only [minor]
        split_ifs with h
        · simp only [h, zero_mul]
        · rfl
      _ = D := by rw [← Finset.sum_mul, productPrior_mass law hlaw, one_mul]
  have hh := movingPrimePattern_signed_bulk_majorant e μ ν prime t small slot perm pattern rep E hE
    hprime hμ hν hnmass hbound G minor hminor seed
  dsimp only at hh
  dsimp only [law] at hmean
  rw [hmean] at hh
  exact hh

end Ostmann

end OAI
