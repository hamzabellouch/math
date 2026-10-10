import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternLogPrimeBulk
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeNorm
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
  (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
  (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
  (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
  (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)
  {tlog : ℕ} (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)

include hB htier hV hBφ hDφ hφ hlip hφout j₀ in
/-- This uniform pointwise estimate allows the extra nonbulk-prime deletion
error to be returned to the initial external law. -/
theorem movingPatternLogPrimeBulkHaar_norm
    (hy : 0 ≤ y) (Kspec : I → ℝ) (hKspec : ∀ i, 0 ≤ Kspec i)
    (hgnorm : ∀ i z, ‖g i z‖ ≤ Kspec i)
    (x : (TreeLeafIndex n × Fin m) → primes) :
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let amp := 2 * (‖movingDataWeight (F false) (E false) (data false)‖ *
      ‖movingDataWeight (F true) (E true) (data true)‖)
    let W := (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
    ‖movingPatternLogPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
      childBound pivotBound hfreq F E outside R r p g twist P Q y ψ X lo hi hlo hhi φ G L U logSlots cb x‖ ≤
        (amp * ∏ i, Kspec i ^ (2 ^ (n + 1))) * W := by
  intro data amp W
  let value := primeBulkValues base (movingPatternBulkEmbedding e slot) x
  have hn : 0 ≤ ∏ j, bulkLogCutoffWeight (fun i => (value i : ℝ)) cb (logSlots j) :=
    Finset.prod_nonneg (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).1)
  have hle : (∏ j, bulkLogCutoffWeight (fun i => (value i : ℝ)) cb (logSlots j)) ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).1)
      (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).2)
  change ‖((_ : ℝ) : ℂ) * movingPatternPrimeBulkHaar e t small slot perm pattern base
    primes hprimes hbase childBound pivotBound hfreq F E outside R r p g twist P Q y
    ψ X lo hi hlo hhi φ G L U x‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hn]
  apply (mul_le_of_le_one_left (norm_nonneg _) hle).trans
  exact movingPatternPrimeBulkHaar_norm e tierB tierC t small slot perm pattern hB htier
    base primes hprimes hbase childBound pivotBound hfreq F E outside R r p g twist P Q y
    j₀ ψ X lo hi V hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U hy Kspec hKspec hgnorm x

end
end Ostmann

end OAI
