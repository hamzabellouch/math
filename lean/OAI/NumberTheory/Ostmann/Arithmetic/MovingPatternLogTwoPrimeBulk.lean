import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternTwoPrimeBulk
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternLogIntegrand

namespace OAI

/-! # Exact selected-prime mean of the original pattern kernel -/

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
  {tlog : ℕ} (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)

/-- This is the original real kernel and its original Page and spectator
averages, evaluated after inserting the selected prime draws. -/
noncomputable def movingPatternLogTwoPrimeBulkHaar (x : (TreeLeafIndex n × Fin m) → primes) : ℂ :=
  let value := primeBulkValues base (movingPatternBulkEmbedding e slot) x
  let hp := primeBulkValues_prime base (movingPatternBulkEmbedding e slot) x hprimes hbase
  let data := movingPatternFinBulkData e n m t small slot perm pattern
  let nodes := fun b => (data b).formulaNodes value (fun i => (hp i).ne_zero)
    childBound pivotBound
    (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq b)
    (.prime false) (.prime true)
  ((∏ j, bulkLogCutoffWeight (fun i => (value i : ℝ)) cb (logSlots j) : ℝ) : ℂ) *
    (movingRealKernelPair value data nodes ψ X lo hi hlo hhi φ G L U *
    (movingFrequencyPrimeAverage value outside F E data nodes R r P Q xg y *
      ∏ i, movingSpectatorPrimeAverage value (p i) (g i) (twist i) data))

include hsmall hR hr hg in
/-- Removing the fixed nonbulk primes is sufficient for the supported
arithmetic identity. The averaging law and its normalizers remain unchanged. -/
theorem movingPatternLogTwoPrimeBulkHaar_mean
    [NeZero (∏ i, bulkResidueModuli r p i)]
    (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
    (c₀ : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ)
    (S deleted : (TreeLeafIndex n × Fin m) → Finset ℕ)
    (hS : ∀ j, S j ⊆ primeCellSupport (∏ i, bulkResidueModuli r p i)
      (fun c : Cell × (ZMod (∏ i, bulkResidueModuli r p i))ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1))
    (hdeleted : ∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → base i ∈ deleted j)
    (hout : ∀ q ∈ outside, q.Prime)
    (hdeletedOut : ∀ j q, q ∈ outside → q ∈ deleted j) :
    let M := ∏ i, bulkResidueModuli r p i
    let label := fun (x : (TreeLeafIndex n × Fin m) → primes) j => primeCellLabel M
      (fun c : Cell × (ZMod M)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) c₀ (x j)
    let K := movingPatternLogIntegrand e tierB tierC t small slot perm pattern hB htier
      (fun i => (base i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hV
      φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U logSlots cb
    let a := fun z => frozenBulkFrequencyPrime base (movingPatternBulkEmbedding e slot) outside
      F E (movingPatternFinBulkData e n m t small slot perm pattern) childBound R r P Q xg y
        (bulkResidueEquiv r p hc z).1 *
      ∏ i, frozenBulkSpectatorPrime base n m t (fun b => movingPatternFiniteSmall e n (small b))
        (movingPatternFiniteSamples e n pattern) (twist i) perm (g i) ((bulkResidueEquiv r p hc z).2 i)
    (∑ x : (TreeLeafIndex n × Fin m) → primes,
      ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) *
        movingPatternLogTwoPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
          childBound pivotBound hfreq F E outside R r p g twist P Q xg y ψ X lo hi hlo hhi φ G L U logSlots cb x) =
    ∑ x : (TreeLeafIndex n × Fin m) → primes,
      ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) *
        (if Function.Injective x then a (fun j => (label x j).2) *
          K (fun j => Real.log (x j : ℕ)) else 0) := by
  intro M label K a
  apply Finset.sum_congr rfl
  intro x _
  by_cases hw : (∏ j, primeSubsetPrior primes (S j \ deleted j) (x j)) = 0
  · simp only [hw, Complex.ofReal_zero, zero_mul]
  · have hx (j) : (x j : ℕ) ∈ S j \ deleted j :=
      primeSubsetPrior_support primes _ _ (Finset.prod_ne_zero_iff.mp hw j (Finset.mem_univ j))
    have hxcell (j) : (x j : ℕ) ∈ primeCellSupport M
        (fun c : Cell × (ZMod M)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) \ deleted j :=
      Finset.mem_sdiff.mpr ⟨hS j (Finset.mem_sdiff.mp (hx j)).1, (Finset.mem_sdiff.mp (hx j)).2⟩
    let value := primeBulkValues base (movingPatternBulkEmbedding e slot) x
    have hp := primeBulkValues_prime base (movingPatternBulkEmbedding e slot) x hprimes hbase
    have hv (i) (hi : i ∉ Set.range (movingPatternBulkEmbedding e slot)) : value i = base i :=
      primeBulkValues_off base (movingPatternBulkEmbedding e slot) x i hi
    have hz (j) : (value (movingPatternBulkEmbedding e slot j) : ZMod M) =
        ((label x j).2 : ZMod M) :=
      primeBulkValues_cell_label base (movingPatternBulkEmbedding e slot) x M u v c₀ deleted hxcell j
    have hid := movingPattern_two_prime_bulk_supported_identity e tierB tierC t small slot perm pattern
      hsmall hB htier base value hv hp childBound pivotBound hfreq F E outside
      (primeBulkValues_cross_of_deleted base (movingPatternBulkEmbedding e slot) x S deleted hx hdeleted)
      (primeBulkValues_outside_coprime base (movingPatternBulkEmbedding e slot) x S deleted
        hprimes hx outside hout hdeletedOut)
      R r hR hr p hc g hg twist (fun j => (label x j).2) hz P Q xg y
      j₀ ψ X lo hi V hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
    dsimp only at hid
    have hinj : Function.Injective (value ∘ movingPatternBulkEmbedding e slot) ↔
        Function.Injective x := primeBulkValues_injective_iff base (movingPatternBulkEmbedding e slot) x
    simp only [hinj] at hid
    apply congrArg (fun z : ℂ => ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) * z)
    have hK : K (fun j => Real.log (x j : ℕ)) =
        ((∏ j, bulkLogCutoffWeight (fun i => (value i : ℝ)) cb (logSlots j) : ℝ) : ℂ) *
          movingPatternBulkIntegrand e tierB tierC t small slot perm pattern hB htier
            (fun i => (base i : ℝ)) childBound pivotBound j₀ ψ X lo hi V hlo hhi hV
            φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U (fun j => Real.log (x j : ℕ)) := by
      have hnat := movingPatternLogIntegrand_nat e tierB tierC t small slot perm pattern hB htier
        childBound pivotBound j₀ ψ X lo hi V hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
        logSlots cb base value hv (fun i => (hp i).ne_zero) hfreq
      have hbaseNat := movingPatternBulkIntegrand_nat e tierB tierC t small slot perm pattern hB htier
        childBound pivotBound j₀ ψ X lo hi V hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
        base value hv (fun i => (hp i).ne_zero) hfreq
      simp only [value, primeBulkValues_at] at hnat hbaseNat
      simpa only [K, hbaseNat] using hnat
    unfold movingPatternLogTwoPrimeBulkHaar
    dsimp only
    rw [hid, hK]
    split_ifs <;> simp only [primeBulkValues_at, a, value, mul_zero]
    ring

end
end Ostmann

end OAI
