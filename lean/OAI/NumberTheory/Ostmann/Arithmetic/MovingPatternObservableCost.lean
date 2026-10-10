import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeObservable
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
  (P : PublishedProgressionInput) (Q : ℕ) (y : ℝ)
  (j₀ : TreeLeafIndex n × Fin m) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
  (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (hV : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
  (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
  (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
  (hφout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)

include hB htier hV hBφ hDφ hφ hlip hφout j₀ in
theorem movingPatternPrimeObservable_norm
    (hy : 0 ≤ y) (Kspec : I → ℝ) (hKspec : ∀ i, 0 ≤ Kspec i)
    (hgnorm : ∀ i z, ‖g i z‖ ≤ Kspec i)
    (x : Fin (N + 1) → primes) :
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let amp := 2 * (‖movingDataWeight (F false) (E false) (data false)‖ *
      ‖movingDataWeight (F true) (E true) (data true)‖)
    let W := (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
    ‖movingPatternPrimeObservable e t small slot perm pattern primes hprimes
      childBound pivotBound hfreq F E outside R r p g twist P Q y
      ψ X lo hi hlo hhi φ G L U x‖ ≤ (amp * ∏ i, Kspec i ^ (2 ^ (n + 1))) * W := by
  dsimp only
  let z := fun j => x (movingPatternBulkEmbedding e slot j)
  have heq : joinBulkNonbulk (movingPatternBulkEmbedding e slot) z (fun i => x i) = x := by
    funext i
    by_cases hi : i ∈ Set.range (movingPatternBulkEmbedding e slot)
    · obtain ⟨j, rfl⟩ := hi
      rw [joinBulkNonbulk_bulk]
    · exact joinBulkNonbulk_nonbulk (movingPatternBulkEmbedding e slot) z
        (fun i => x i) ⟨i, hi⟩
  have ho := movingPatternPrimeObservable_join e t small slot perm pattern primes hprimes
    childBound pivotBound hfreq F E outside R r p g twist P Q y
    ψ X lo hi hlo hhi φ G L U x z
  rw [heq] at ho
  rw [ho]
  exact movingPatternPrimeBulkHaar_norm e tierB tierC t small slot perm pattern hB htier
    (fun i => (x i : ℕ)) primes hprimes (fun i _ => hprimes _ (x i).property)
    childBound pivotBound hfreq F E outside R r p g twist P Q y j₀ ψ X lo hi V hlo hhi hV
    φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U hy Kspec hKspec hgnorm z

end

/-- The full pointwise cost from the actual observable is uniform over
patterns and prime assignments at fixed depth. -/
theorem movingPattern_pointwise_cost (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A lo hi B D F : ℝ) (hA : 0 ≤ A) (hhi : lo ≤ hi) (hF : 0 ≤ F) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → let m := spectatorBulkCount k L
      ∀ (p : Fin m → ℕ) (amp : ℝ),
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      0 ≤ amp → amp ≤ Real.exp (F * m) →
      (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
        Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
  obtain ⟨Cw, hCw, hkernel⟩ := movingPatternKernelBudget_spectatorScale ψ n r₀ k
    A lo hi B D hA hhi
  let K := (F + 1) * ((k : ℝ) ^ 4 + 1)
  let C := max Cw ((((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K)
  have hCwC : Cw ≤ C := le_max_left _ _
  have hCs : (((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K ≤ C := le_max_right _ _
  refine ⟨C, hCw.trans hCwC, ?_⟩
  intro L hL
  dsimp only
  intro p amp hp hamp0 hamp
  let m := spectatorBulkCount k L
  let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
    (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  have hL0 : 0 ≤ L := by linarith
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hFk : F * (k : ℝ) ^ 4 ≤ K := by
    dsimp only [K]
    nlinarith [pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4]
  have hkK : (k : ℝ) ^ 4 ≤ K := by
    dsimp only [K]
    nlinarith [mul_nonneg hF (pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4)]
  have hm := spectatorBulkCount_upper k L hL0
  have hmK : (m : ℝ) ≤ K * L := hm.trans (mul_le_mul_of_nonneg_right hkK hL0)
  have hampK : amp ≤ Real.exp (K * L) := hamp.trans (Real.exp_le_exp.mpr (by
    exact (mul_le_mul_of_nonneg_left hm hF).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hFk hL0])))
  have hspec := moving_spectator_linear_cost n m p K L amp hK hL0 hamp0 hmK hampK hp
  have hspec' : amp * (∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) ≤
      Real.exp (C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    apply hspec.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCs hL0) (Real.exp_nonneg _)
  have hW : W ≤ Real.exp (C * L ^ 2) := by
    apply (bulkKernelPair_smooth_le_budget ψ (Real.exp (A * m)) lo hi n
      (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D).trans
    exact (hkernel L hL).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hCwC (sq_nonneg L)))
  exact (mul_le_mul hspec' hW (sq_nonneg _) (Real.exp_nonneg _)).trans_eq (by
    rw [← Real.exp_add, add_comm])

end Ostmann

end OAI
