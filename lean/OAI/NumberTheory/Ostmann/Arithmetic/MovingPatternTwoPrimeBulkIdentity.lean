import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternIntegrand
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeBulkArithmetic

namespace OAI

/-! # Return the separated bulk kernel to the original supported histories -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- An exact identity for every original prime tuple.  Its bulk collision
indicator is derived from the original regular-product support, before any
prime replacement or change of normalization. -/
theorem movingPattern_two_prime_bulk_supported_identity {B C I : Type*} [Fintype I] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (base value : Fin (N + 1) → ℕ)
    (hv : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), value i = base i)
    (hprime : ∀ i, (value i).Prime) (childBound pivotBound : ℕ → ℕ)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
    (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
    (outside : List ℕ)
    (hcross : ∀ i j, bulkIndexPredicate (movingPatternBulkEmbedding e slot) i ≠
      bulkIndexPredicate (movingPatternBulkEmbedding e slot) j → value i ≠ value j)
    (hout : ∀ j p, p ∈ outside → (value (movingPatternBulkEmbedding e slot j)).Coprime p)
    (R : ℤ) (r : ℕ) [NeZero r]
    (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
    (hr : R ^ (n + 1) ∣ (r : ℤ))
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (twist : ∀ i, Bool → (ZMod (p i))ˣ)
    (z : TreeLeafIndex n × Fin m → (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hz : ∀ j, (value (movingPatternBulkEmbedding e slot j) : ZMod (∏ i, bulkResidueModuli r p i)) =
      (z j : ZMod _))
    (P : PublishedProgressionInput) (Q : ℕ) (xg y : ℝ)
    (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ) :
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let nodes := fun b => (data b).formulaNodes value (fun i => (hprime i).ne_zero)
      childBound pivotBound
      (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq b)
      (.prime false) (.prime true)
    movingRealKernelPair value data nodes ψ X lo hi hlo hhi φ G L U *
      (movingFrequencyPrimeAverage value outside F E data nodes R r P Q xg y *
        ∏ i, movingSpectatorPrimeAverage value (p i) (g i) (twist i) data) =
      if Function.Injective (value ∘ movingPatternBulkEmbedding e slot) then
        movingPatternBulkIntegrand e tierB tierC t small slot perm pattern hB htier
          (fun i => (base i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hV
          φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
          (fun j => Real.log (value (movingPatternBulkEmbedding e slot j) : ℝ)) *
        (frozenBulkFrequencyPrime base (movingPatternBulkEmbedding e slot) outside
          F E data childBound R r P Q xg y (bulkResidueEquiv r p hc z).1 *
          ∏ i, frozenBulkSpectatorPrime base n m t (fun b => movingPatternFiniteSmall e n (small b))
            (movingPatternFiniteSamples e n pattern) (twist i) perm (g i)
            ((bulkResidueEquiv r p hc z).2 i))
      else 0 := by
  intro data nodes
  by_cases hinj : Function.Injective (value ∘ movingPatternBulkEmbedding e slot)
  · rw [ite_eq_left hinj]
    rw [movingPatternBulkIntegrand_nat e tierB tierC t small slot perm pattern hB htier
      childBound pivotBound j₀ ψ X lo hi V hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
      base value hv (fun i => (hprime i).ne_zero) hfreq]
    congr 1
    exact movingPattern_supported_prime_arithmetic e tierB tierC t small slot perm pattern hsmall hB htier
      base value hv F E outside childBound pivotBound hprime
      (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq)
      hinj hcross hout R r hR hr p hc g hg twist z hz P Q xg y
  · rw [ite_eq_right hinj]
    have hzero := movingPattern_prime_arithmetic_collision_gate e t small slot perm pattern value hprime
      outside F E nodes R r P Q xg y (∏ i, movingSpectatorPrimeAverage value (p i) (g i) (twist i) data)
    dsimp only at hzero
    rw [ite_eq_right hinj] at hzero
    rw [hzero, mul_zero]

end Ostmann

end OAI
