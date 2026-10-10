import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternLogTwoPrimeNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternLogTwoPrimeObservable
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternKernelGain

namespace OAI

/-! # The actual observable and its uniform pointwise arithmetic cost -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

section
variable {B C I : Type*} [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
  (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
  (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
  (pattern : Bool × MovingSampleIndex n → C)
  (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime]
  (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ)
  (P : PublishedProgressionInput) (Q : ℕ) (xg y : ℝ)
  (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
  (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
  (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
  (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)
  {tlog : ℕ} (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)

include hB htier hV hBφ hDφ hφ hlip hφout j₀ in
theorem movingPatternLogTwoPrimeObservable_norm
    (hxg : 0 ≤ xg) (hy : 0 ≤ y) (Kspec : I → ℝ) (hKspec : ∀ i, 0 ≤ Kspec i)
    (hgnorm : ∀ i z, ‖g i z‖ ≤ Kspec i)
    (x : Fin (N + 1) → primes) :
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let amp := 4 * (‖movingDataWeight (F false) (E false) (data false)‖ *
      ‖movingDataWeight (F true) (E true) (data true)‖)
    let W := (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
    ‖movingPatternLogTwoPrimeObservable e t small slot perm pattern primes hprimes
      childBound pivotBound hfreq F E outside R r p g twist P Q xg y
      ψ X lo hi hlo hhi φ G L U logSlots cb x‖ ≤ (amp * ∏ i, Kspec i ^ (2 ^ (n + 1))) * W := by
  dsimp only
  let z := fun j => x (movingPatternBulkEmbedding e slot j)
  have heq : joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => x i) = x := by
    funext i
    by_cases hi : i ∈ Set.range (movingPatternBulkEmbedding e slot)
    · obtain ⟨j, rfl⟩ := hi
      rw [joinBulkNonbulk_bulk]
    · exact joinBulkNonbulk_nonbulk (movingPatternBulkEmbedding e slot) z
        (fun i => x i) ⟨i, hi⟩
  have ho := movingPatternLogTwoPrimeObservable_join e t small slot perm pattern primes hprimes
    childBound pivotBound hfreq F E outside R r p g twist P Q xg y
    ψ X lo hi hlo hhi φ G L U logSlots cb x z
  rw [heq] at ho
  rw [ho]
  exact movingPatternLogTwoPrimeBulkHaar_norm e tierB tierC t small slot perm pattern hB htier
    (fun i => (x i : ℕ)) primes hprimes (fun i _ => hprimes _ (x i).property)
    childBound pivotBound hfreq F E outside R r p g twist P Q xg y j₀ ψ X lo hi V hlo hhi hV
    φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U logSlots cb hxg hy Kspec hKspec hgnorm z

end

end Ostmann

end OAI
