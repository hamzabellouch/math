import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternLogTwoPrimeObservable
import OAI.NumberTheory.Ostmann.Arithmetic.MovingLogPrimeAverage
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPairedLogSlots
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkBudgets

namespace OAI

/-! # The actual initial leaf weights in the pattern prime observable -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

section
variable {B C I : Type*} [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
  (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
  (E : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ) (P : PublishedProgressionInput) (Q : ℕ) (xg y : ℝ)
  (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (L U : ℝ)
  (tier : Fin (N + 1) → ℕ) (k : ℕ) (cb cd : ℝ)

/-- Exact identification with the retained-log observable. The outside
spectator profile is a scalar; every variable terminal factor remains inside. -/
theorem movingPatternTwoPrimeObservable_log_leaf (x : Fin (N + 1) → primes) :
    let value := fun i => (x i : ℕ)
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    movingPatternTwoPrimeObservable e t small slot perm pattern primes hprimes
      childBound pivotBound hfreq
      (fun b {_} T s => (movingBulkLeafLogWeight value tier k outside cb cd T : ℂ) * F b T s)
      E outside R r p g twist P Q xg y ψ X lo hi hlo hhi φ G L U x =
    (logCellProfile ((outside.map (fun p => Real.log (p : ℝ))).sum - cd) ^
      (2 ^ n + 2 ^ n) : ℝ) *
      movingPatternLogTwoPrimeObservable e t small slot perm pattern primes hprimes
        childBound pivotBound hfreq F E outside R r p g twist P Q xg y
        ψ X lo hi hlo hhi φ G L U (movingPairedLogSlots tier k T) cb x := by
  intro value T
  let nodes := fun b => (T b).formulaNodes value
    (fun i => (hprimes _ (x i).property).ne_zero) childBound pivotBound
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq b)
    (.prime false) (.prime true)
  change movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G L U *
    (movingFrequencyPrimeAverage value outside
      (fun b {_} T s => (movingBulkLeafLogWeight value tier k outside cb cd T : ℂ) * F b T s)
      E T nodes R r P Q xg y * ∏ i, movingSpectatorPrimeAverage value (p i) (g i) (twist i) T) = _
  rw [movingFrequencyPrimeAverage_bulk_log value tier k outside cb cd F E T nodes R]
  rw [movingBulkPairLogWeight_eq_cutoff_product value tier
    (fun i => (hprimes _ (x i).property).pos) k outside cb cd T]
  change _ = (logCellProfile ((outside.map (fun p => Real.log (p : ℝ))).sum - cd) ^
      (2 ^ n + 2 ^ n) : ℝ) *
    (((∏ j, bulkLogCutoffWeight (fun i => (value i : ℝ)) cb
      (movingPairedLogSlots tier k T j) : ℝ) : ℂ) *
      (movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G L U *
        (movingFrequencyPrimeAverage value outside F E T nodes R r P Q xg y *
          ∏ i, movingSpectatorPrimeAverage value (p i) (g i) (twist i) T)))
  unfold movingPairedLogSlots
  ring

end

/-- The concrete pattern automatically meets the retained-log comparison's
terminal length bound. -/
theorem movingPattern_log_slot_lengths {B C : Type*} {N n m r₀ : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
    (tier : Fin (N + 1) → ℕ) (k : ℕ) (hsmall : ∀ b, MovingLeafLengthLE n (small b) r₀) :
    ∀ j, (movingPairedLogSlots tier k
      (movingPatternFinBulkData e n m t small slot perm pattern) j).length ≤
        2 ^ n * (r₀ + m + 4 * n) :=
  movingPairedLogSlots_length_le tier k _ _
    (movingPatternFinBulkData_regular_length e t small slot perm pattern hsmall)

end Ostmann

end OAI
