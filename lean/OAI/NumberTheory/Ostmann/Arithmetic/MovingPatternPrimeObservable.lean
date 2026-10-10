import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeBulk
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkMean

namespace OAI

/-! # The literal prime observable in the original nonbulk Fubini formula -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

section
variable {B C I : Type*} [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
  (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ) (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (L U : ℝ)

/-- The coefficient before selecting or conditioning any of its bulk
coordinates. All original frequency and coprimality gates are retained. -/
noncomputable def movingPatternPrimeObservable (x : Fin (N + 1) → primes) : ℂ :=
  let value := fun i => (x i : ℕ)
  let data := movingPatternFinBulkData e n m t small slot perm pattern
  let nodes := fun b => (data b).formulaNodes value
    (fun i => (hprimes _ (x i).property).ne_zero) childBound pivotBound
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq b)
    (.prime false) (.prime true)
  movingRealKernelPair value data nodes ψ X lo hi hlo hhi φ G L U *
    (movingFrequencyPageAverage value outside F E data nodes R r P Q y *
      ∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) data)

theorem movingPatternPrimeObservable_join (base : Fin (N + 1) → primes)
    (z : TreeLeafIndex n × Fin m → primes) :
    movingPatternPrimeObservable e t small slot perm pattern primes hprimes
      childBound pivotBound hfreq F E outside R r p g twist P Q y ψ X lo hi hlo hhi φ G L U
      (joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => base i)) =
    movingPatternPrimeBulkHaar e t small slot perm pattern (fun i => (base i : ℕ)) primes
      hprimes (fun i _ => hprimes _ (base i).property) childBound pivotBound hfreq F E outside
      R r p g twist P Q y ψ X lo hi hlo hhi φ G L U z := by
  have hv : (fun i => (joinBulkNonbulk (A := primes) (movingPatternBulkEmbedding e slot) z
      (fun j => base j) i : ℕ)) =
      primeBulkValues (fun i => (base i : ℕ)) (movingPatternBulkEmbedding e slot) z := by
    funext i
    by_cases hi : i ∈ Set.range (movingPatternBulkEmbedding e slot)
    · obtain ⟨j, rfl⟩ := hi
      rw [joinBulkNonbulk_bulk, primeBulkValues_at]
    · rw [joinBulkNonbulk_nonbulk (movingPatternBulkEmbedding e slot) z
        (fun j => base j) ⟨i, hi⟩, primeBulkValues_off _ _ _ i hi]
  let eval : {v : Fin (N + 1) → ℕ // ∀ i, v i ≠ 0} → ℂ := fun v =>
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let nodes := fun b => (data b).formulaNodes v.val v.property childBound pivotBound
      (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq b)
      (.prime false) (.prime true)
    movingRealKernelPair v.val data nodes ψ X lo hi hlo hhi φ G L U *
      (movingFrequencyPageAverage v.val outside F E data nodes R r P Q y *
        ∏ i, movingSpectatorHaarAverage v.val (p i) (g i) (twist i) data)
  let left : {v : Fin (N + 1) → ℕ // ∀ i, v i ≠ 0} :=
    ⟨fun i => (joinBulkNonbulk (A := primes) (movingPatternBulkEmbedding e slot) z
        (fun j => base j) i : ℕ),
      fun i => (hprimes _ ((joinBulkNonbulk (A := primes)
        (movingPatternBulkEmbedding e slot) z (fun j => base j)) i).property).ne_zero⟩
  let right : {v : Fin (N + 1) → ℕ // ∀ i, v i ≠ 0} :=
    ⟨primeBulkValues (fun i => (base i : ℕ)) (movingPatternBulkEmbedding e slot) z,
      fun i => (primeBulkValues_prime (fun i => (base i : ℕ))
        (movingPatternBulkEmbedding e slot) z hprimes
        (fun i _ => hprimes _ (base i).property) i).ne_zero⟩
  change eval left = eval right
  exact congrArg eval (Subtype.ext hv)

/-- This is exactly the selected-coordinate average used by the signed
pattern majorant, under the initial word law. -/
theorem movingPatternBulkMean_primeObservable (base : Fin (N + 1) → primes)
    (ν : B → primes → ℝ) (initial : (TreeLeafIndex n × Fin m) → Finset ℕ)
    (hν : ∀ j, ν (slot j) = primeSubsetPrior primes (initial j)) :
    movingPatternBulkMean e ν slot
      (movingPatternPrimeObservable e t small slot perm pattern primes hprimes
        childBound pivotBound hfreq F E outside R r p g twist P Q y ψ X lo hi hlo hhi φ G L U) base =
    ∑ z : TreeLeafIndex n × Fin m → primes,
      ((∏ j, primeSubsetPrior primes (initial j) (z j) : ℝ) : ℂ) *
        movingPatternPrimeBulkHaar e t small slot perm pattern (fun i => (base i : ℕ)) primes
          hprimes (fun i _ => hprimes _ (base i).property) childBound pivotBound hfreq F E outside
          R r p g twist P Q y ψ X lo hi hlo hhi φ G L U z := by
  unfold movingPatternBulkMean
  apply Finset.sum_congr rfl
  intro z _
  rw [movingPatternPrimeObservable_join]
  simp only [hν]

end
end Ostmann

end OAI
