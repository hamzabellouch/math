import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeBulk
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternSeparatedBound
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenSpectatorNorm

namespace OAI

/-! # The separated estimate for the literal original prime mean -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

section
variable {B C Cell : Type*} [Fintype Cell] {N n m : ℕ}
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
  (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
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

include hsmall hB htier hR hr hg hV hBφ hDφ hφ hlip hφout j₀ in
/-- The original Page/spectator kernel now has a signed bound under its
literal deleted prime prior. Its frequency and pointwise spectator bounds
are derived; the remaining local signed mean is exactly the quartet input. -/
theorem PublishedProgressionInput.movingPattern_original_prime_bound
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (r₀ : ℕ) (hsmallLen : ∀ b, MovingLeafLengthLE n (small b) r₀)
    (hy : 0 ≤ y) (hQ : 2 ≤ Q) (hMQ : (∏ i, bulkResidueModuli r p i) ≤ Q)
    (hpage : pageAtModulus (∏ i, bulkResidueModuli r p i) (selectedPageZero P Q) =
      pageAtModulus r (selectedPageZero P Q))
    (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
    (hu : ∀ j c, 1 ≤ u j c) (huv : ∀ j c, u j c ≤ v j c)
    (hshort : ∀ j c, v j c ≤ u j c + 1)
    (hmassCell : ∀ j c (a : (ZMod (∏ i, bulkResidueModuli r p i))ˣ),
      ∑ q ∈ primeLogCellSet (∏ i, bulkResidueModuli r p i) a.val.val (u j c) (v j c),
        (q : ℝ)⁻¹ ≤ 2)
    (c₀ : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (hP : ∀ j, primeCellSupport (∏ i, bulkResidueModuli r p i)
      (fun c : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) ⊆ primes)
    (hsep : ∀ j (c d : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ), c ≠ d →
      ¬Nat.ModEq (∏ i, bulkResidueModuli r p i) c.2.val.val d.2.val.val ∨
        v j c.1 ≤ u j d.1 ∨ v j d.1 ≤ u j c.1)
    (deleted : (TreeLeafIndex n × Fin m) → Finset ℕ)
    (hdeleted : ∀ j, (∑ q ∈ primeCellSupport (∏ i, bulkResidueModuli r p i)
      (fun c : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) \ deleted j, (q : ℝ)⁻¹) ≠ 0)
    (hdeletedBase : ∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → base i ∈ deleted j)
    (hout : ∀ q ∈ outside, q.Prime) (hdeletedOut : ∀ j q, q ∈ outside → q ∈ deleted j)
    (Kspec : Fin m → ℝ) (hKspec : ∀ i, 0 ≤ Kspec i)
    (hgnorm : ∀ i z, ‖g i z‖ ≤ Kspec i)
    (δ : ℝ) (hδ : 0 ≤ δ) (H T : ℝ) :
    let data := movingPatternFinBulkData e n m t small slot perm pattern
    let freq := frozenBulkFrequencyFactor base (movingPatternBulkEmbedding e slot) outside
      F E data childBound R r P Q y
    let spec := fun i => frozenBulkSpectatorHaar base n m t
      (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
      (twist i) perm (g i)
    let A := 2 * (‖movingDataWeight (F false) (E false) (data false)‖ *
      ‖movingDataWeight (F true) (E true) (data true)‖)
    let W := (movingFourierVariationBudget ψ V lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
    let M := ∏ i, bulkResidueModuli r p i
    let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1)
    let Z := fun j => (∑ q ∈ S j \ deleted j, (q : ℝ)⁻¹)⁻¹
    let a := fun z => freq (bulkResidueEquiv r p hc z).1 *
      ∏ i, spec i ((bulkResidueEquiv r p hc z).2 i)
    let err := fun c : (TreeLeafIndex n × Fin m) → Cell =>
      2 ^ Fintype.card (TreeLeafIndex n × Fin m) * ∑ j,
        bulkKernelPairComparisonBudget ψ V lo hi n
          (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 Bφ Dφ *
          bulkPrimeErrorFactor P Q (u j (c j))
    (∀ i, ‖(Fintype.card ((TreeLeafIndex n × Fin m) → (ZMod (p i))ˣ) : ℂ)⁻¹ *
      ∑ z, spec i z‖ ≤ δ) →
    (∀ j, Z j * ∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹ ≤ 2) →
    (∀ j, Z j ≤ Real.exp H) →
    (∀ j q, q ∈ S j \ deleted j → Real.exp T ≤ (q : ℝ)) →
    ‖∑ x : (TreeLeafIndex n × Fin m) → primes,
      ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) *
        movingPatternPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
          childBound pivotBound hfreq F E outside R r p g twist P Q y ψ X lo hi hlo hhi φ G L U x‖ ≤
      (W * A) * 4 ^ Fintype.card (TreeLeafIndex n × Fin m) * δ ^ m +
        (∏ j, Z j) * ∑ c : (TreeLeafIndex n × Fin m) → Cell, ∑ z, ‖a z‖ * err c +
        (A * (∏ i, Kspec i ^ (2 ^ (n + 1))) * W) *
          (Fintype.card (TreeLeafIndex n × Fin m) : ℝ) ^ 2 * Real.exp (H - T) +
        (A * (∏ i, Kspec i ^ (2 ^ (n + 1))) * W) *
          ((∏ j, (1 + Z j * ∑ q ∈ S j ∩ deleted j, (q : ℝ)⁻¹)) - 1) := by
  intro data freq spec A W M S Z a err hlocal hmass hZ hlow
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hf (z) : ‖freq z‖ ≤ A :=
    frozenBulkFrequencyFactor_norm_le base (movingPatternBulkEmbedding e slot) outside
      F E data childBound R r P Q y hy z
  have hspec (i) (z) : ‖spec i z‖ ≤ Kspec i ^ (2 ^ (n + 1)) :=
    frozenBulkSpectatorHaar_norm_le base n m t _ _ (twist i) perm (g i) (Kspec i)
      (hKspec i) (hgnorm i) z
  have heq := movingPatternPrimeBulkHaar_mean e tierB tierC t small slot perm pattern hsmall hB htier
    base primes hprimes hbase childBound pivotBound hfreq F E outside R r hR hr p hc g hg twist
    P Q y j₀ ψ X lo hi V hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
    u v c₀ S deleted (fun _ => Finset.Subset.refl _) hdeletedBase hout hdeletedOut
  dsimp only at heq
  rw [heq]
  have hb := P.movingPattern_separated_kernel_bound e tierB tierC t small slot perm pattern hB htier
    hsmallLen base childBound pivotBound j₀ ψ X lo hi V hlo hhi hV φ G Bφ Dφ hBφ hDφ
    hφ hlip hφout L U r p hc freq spec A hA hf Q hQ hMQ hpage primes u v hu huv hshort
    hmassCell c₀ hP hsep deleted hdeleted δ hδ H T (fun i => Kspec i ^ (2 ^ (n + 1)))
    (fun i => pow_nonneg (hKspec i) _)
  exact hb hlocal hspec hmass hZ hlow

end
end Ostmann

end OAI
