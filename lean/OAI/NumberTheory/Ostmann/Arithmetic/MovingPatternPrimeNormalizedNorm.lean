import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeFrozenNorm
import OAI.NumberTheory.Ostmann.Characters.NormalizedResidueIndicator

namespace OAI

/-! # The two-prime absolute norm for the normalized spectator transforms -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPattern_normalized_same_assignment_prime_norm {B C I : Type*} [Fintype I] {N₀ n m : ℕ}
    (e : Fin (N₀ + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (S : Finset ℤ) (t : FrequencyTree (S × S) n) (R N V : ℕ)
    [NeZero (R ^ (n - 1 + 2))]
    (hS : ∀ s ∈ S, s ≠ 0) (hN : ∀ s ∈ S, s.natAbs ≤ N)
    (hR : ∀ b (j : Fin (2 ^ n - 1)),
      (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (pattern : Bool × MovingSampleIndex n → C)
    (hsmall : ∀ b i, i ∈ flattenMovingSlots n (small b) → i ∉ Set.range slot)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (base : Fin (N₀ + 1) → ℕ)
    (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), IsCoprime (base i : ℤ) (R : ℤ))
    (F : Bool → {k : ℕ} → MovingSlotData (Fin (N₀ + 1)) k → ℤ → ℂ)
    (hF : ∀ b s regular, ‖F b (.leaf s regular) s‖ ≤ if s.natAbs ≤ V then 1 else 0)
    (D : ℝ) (hD : 0 ≤ D)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D) (hm : 0 < m)
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    [NeZero (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli (R ^ (n - 1 + 2)) p i).Coprime
      (bulkResidueModuli (R ^ (n - 1 + 2)) p j))) (hp : ∀ i, 3 ≤ p i)
    (hfreq : ∀ i b, movingGiantFrequencyUnits (p i) n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)))
    (hsmallp : ∀ i b j, j ∈ flattenMovingSlots n (small b) →
      (base (e.symm (.inl j)) : ZMod (p i)) ≠ 0)
    (hasamples : ∀ i c, (base (e.symm (.inr c)) : ZMod (p i)) ≠ 0)
    (sets : ∀ i, Finset (ZMod (p i)))
    (hsets : ∀ i, (sets i).Nonempty) (hsetsLt : ∀ i, (sets i).card < p i)
    (twist : ∀ i, Bool → (ZMod (p i))ˣ) (outside : List ℕ) (childBound : ℕ → ℕ)
    (input : PublishedProgressionInput) (Qfreq Qbulk : ℕ) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) (hYbulk : ∀ j, 0 ≤ Ybulk j) :
    let ts := fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)
    let data := movingPatternFinBulkData e n m ts small slot (Equiv.refl _) pattern
    let freq := frozenBulkFrequencyPrime base (movingPatternBulkEmbedding e slot) outside
      F (fun _ _ _ _ _ => 1) data childBound R (R ^ (n - 1 + 2)) input Qfreq X Y
    let spec := fun i => frozenBulkSpectatorPrime base n m ts
      (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
      (twist i) (Equiv.refl _) (normalizedResidueTransform (sets i))
    let M := ∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i
    let A := fun z => freq (bulkResidueEquiv (R ^ (n - 1 + 2)) p hc z).1 *
      ∏ i, spec i ((bulkResidueEquiv (R ^ (n - 1 + 2)) p hc z).2 i)
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod M)ˣ) : ℝ)⁻¹ *
      (∑ z : TreeLeafIndex n × Fin m → (ZMod M)ˣ,
        ‖A z * ∏ j, pageGiantWeight input Qbulk M (z j).val.val (Ybulk j)‖) ≤
      ((2 : ℝ) ^ (2 ^ n * m) * 4 * 3 ^ (2 ^ n * Fintype.card I)) *
        (frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
          ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) := by
  exact movingPattern_same_assignment_prime_norm e tierB tierC S t R N V hS hN hR small slot pattern
    hsmall hB htier base hbase F hF D hD hdiv hm p hc hp hfreq hsmallp hasamples
    (fun i => normalizedResidueTransform (sets i))
    (fun i => normalizedResidueTransform_zero (sets i))
    (fun i => (normalizedResidueTransform_energy (sets i) (hsets i) (hsetsLt i)).le)
    twist outside childBound input Qfreq Qbulk X Y hX hY Ybulk hYbulk

end Ostmann

end OAI
