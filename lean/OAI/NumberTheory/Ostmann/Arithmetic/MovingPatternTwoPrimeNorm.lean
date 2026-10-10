import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternTwoPrimeBulk
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimePointwiseNorm

namespace OAI

/-! # Pointwise bound for the literal original prime observable -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

section
variable {B C Cell I : Type*} [Fintype Cell] [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
  (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
  (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot)
  (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
  (base : Fin (N + 1) → ℕ) (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), (base i).Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
  (hr : R ^ (n + 1) ∣ (r : ℤ))
  (p : I → ℕ) [∀ i, Fact (p i).Prime]
  (hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
  (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ)
  (P : PublishedProgressionInput) (Q : ℕ) (xg y : ℝ)
  (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
  (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
  (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
  (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)

include hB htier hV hBφ hDφ hφ hlip hφout j₀ in
/-- This uniform pointwise estimate allows the extra nonbulk-prime deletion
error to be returned to the initial external law. -/
theorem movingPatternTwoPrimeBulkHaar_norm
    (hxg : 0 ≤ xg) (hy : 0 ≤ y) (Kspec : I → ℝ) (hKspec : ∀ i, 0 ≤ Kspec i)
    (hgnorm : ∀ i z, ‖g i z‖ ≤ Kspec i)
    (x : (TreeLeafIndex n × Fin m) → primes) :
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let amp := 4 * (‖movingDataWeight (F false) (E false) (data false)‖ *
      ‖movingDataWeight (F true) (E true) (data true)‖)
    let W := (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
    ‖movingPatternTwoPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
      childBound pivotBound hfreq F E outside R r p g twist P Q xg y ψ X lo hi hlo hhi φ G L U x‖ ≤
        (amp * ∏ i, Kspec i ^ (2 ^ (n + 1))) * W := by
  intro data amp W
  let value := primeBulkValues base (movingPatternBulkEmbedding e slot) x
  have hp := primeBulkValues_prime base (movingPatternBulkEmbedding e slot) x hprimes hbase
  have hv : ∀ i, value i ≠ 0 := fun i => (hp i).ne_zero
  have hf := movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq
  let nodes := fun b => (data b).formulaNodes value hv childBound pivotBound (hf b)
    (.prime false) (.prime true)
  have hk : ‖movingRealKernelPair value data nodes ψ X lo hi hlo hhi φ G L U‖ ≤ W := by
    rw [← realValueKernelPair_nat value hv childBound pivotBound data hf]
    exact movingPattern_kernel_norm_le e tierB tierC t small slot perm pattern hB htier
      (fun i => (value i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hV
      φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
  have hfr : ‖movingFrequencyPrimeAverage value outside F E data nodes R r P Q xg y‖ ≤ amp :=
    movingFrequencyPrimeAverage_norm_le value outside F E data nodes R r P Q xg y hxg hy
  have hs : ‖∏ i, movingSpectatorPrimeAverage value (p i) (g i) (twist i) data‖ ≤
      ∏ i, Kspec i ^ (2 ^ (n + 1)) := by
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ =>
      movingSpectatorPrimeAverage_norm_le value (p i) (g i) (twist i) data
        (Kspec i) (hKspec i) (hgnorm i))
  change ‖movingRealKernelPair value data nodes ψ X lo hi hlo hhi φ G L U *
    (movingFrequencyPrimeAverage value outside F E data nodes R r P Q xg y *
      ∏ i, movingSpectatorPrimeAverage value (p i) (g i) (twist i) data)‖ ≤ _
  simp only [norm_mul]
  calc
    _ ≤ W * (amp * ∏ i, Kspec i ^ (2 ^ (n + 1))) :=
      mul_le_mul hk (mul_le_mul hfr hs (norm_nonneg _) (by dsimp only [amp]; positivity))
        (by positivity) (sq_nonneg _)
    _ = _ := mul_comm _ _

end
end Ostmann

end OAI
