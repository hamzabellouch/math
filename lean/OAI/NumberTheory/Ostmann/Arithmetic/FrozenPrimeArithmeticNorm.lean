import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeAverages
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenArithmeticNorm

namespace OAI

/-! # The same-assignment arithmetic norm under the two-prime giant law -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def frozenBulkFrequencyPrime {σ J : Type*}
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (childBound : ℕ → ℕ)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput)
    (Q : ℕ) (x y : ℝ) (a : J → (ZMod r)ˣ) : ℂ :=
  (if ∀ b, movingNonbulkOutsidePairwise base (bulkIndexPredicate slot) outside (T b) ∧
      (T b).FrequencyBounds childBound then (1 : ℂ) else 0) *
    movingFrequencyCorePrimeAverage (Function.extend slot (fun j => (a j).val.val) base)
      F E T R r input Q x y

section
variable {σ : Type*} (base : σ → ℕ) (tier : σ → ℕ) (S : Finset ℤ) (n m R : ℕ)
  [NeZero (R ^ (n - 1 + 2))] (t : FrequencyTree (S × S) n)
  (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ b (j : Fin (2 ^ n - 1)),
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
  (slot : (TreeLeafIndex n × Fin m) ↪ σ)
  (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n)
  (hslot : ∀ j, n ≤ tier (slot j))
  (hsmall : ∀ b i, i ∈ flattenMovingSlots n (small b) → i ∉ Set.range slot)
  (ha : ∀ b, (a b).Levels tier)
  (hbase : ∀ i ∉ Set.range slot, IsCoprime (base i : ℤ) (R : ℤ))
  (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
  (N : ℕ) (D : ℝ) (hD : 0 ≤ D) (hN : ∀ s ∈ S, s.natAbs ≤ N)
  (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
  (hm : 0 < m)

include hslot hsmall ha hbase hS hR hD hN hdiv hm in
/-- The retained fixed support mask can only decrease the bulk norm. -/
theorem frozenBulkFrequencyPrime_mean_le
    (outside : List ℕ) (childBound : ℕ → ℕ) (input : PublishedProgressionInput)
    (Q : ℕ) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    let T := fun b => buildMovingSlotData n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      (small b) (bulkSlotLeaves n m slot) (a b)
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ) : ℝ)⁻¹ *
        (∑ z : TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ,
          ‖frozenBulkFrequencyPrime base slot outside F E T childBound R
            (R ^ (n - 1 + 2)) input Q X Y z‖) ≤
      4 * ((‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) *
      ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) := by
  intro T
  apply le_trans _ (frequencyModelBulkPrime_mean_le base tier S n m R t hS hR slot small a
    hslot hsmall ha hbase F E N D hD hN hdiv hm input Q X Y hX hY)
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro z _
  unfold frozenBulkFrequencyPrime
  split_ifs
  · rw [one_mul]
  · simpa only [zero_mul, norm_zero] using norm_nonneg
      (movingFrequencyCorePrimeAverage (Function.extend slot (fun j => (z j).val.val) base)
        F E T R (R ^ (n - 1 + 2)) input Q X Y)

end

section
variable {σ I : Type*} [Fintype I] (base : σ → ℕ) (tier : σ → ℕ) (S : Finset ℤ) (n m R : ℕ)
  [NeZero (R ^ (n - 1 + 2))] (t : FrequencyTree (S × S) n)
  (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ b (j : Fin (2 ^ n - 1)),
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
  (slot : (TreeLeafIndex n × Fin m) ↪ σ)
  (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n)
  (hslot : ∀ j, n ≤ tier (slot j))
  (hsmall : ∀ b i, i ∈ flattenMovingSlots n (small b) → i ∉ Set.range slot)
  (ha : ∀ b, (a b).Levels tier)
  (hbase : ∀ i ∉ Set.range slot, IsCoprime (base i : ℤ) (R : ℤ))
  (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
  (N : ℕ) (D : ℝ) (hD : 0 ≤ D) (hN : ∀ s ∈ S, s.natAbs ≤ N)
  (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
  (hm : 0 < m)

include hslot hsmall ha hbase hS hR hD hN hdiv hm in
/-- The nonnegative original arithmetic model retains the frequency saving,
the absolute spectator moments and the exact number of bulk Page factors. -/
theorem frozenArithmetic_same_assignment_prime_norm
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    [NeZero (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli (R ^ (n - 1 + 2)) p i).Coprime
      (bulkResidueModuli (R ^ (n - 1 + 2)) p j)))
    (hp : ∀ i, 3 ≤ p i)
    (hfreq : ∀ i b, movingGiantFrequencyUnits (p i) n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)))
    (hsmallp : ∀ i b, ((treeLeafProduct n (movingSlotValues base n (small b)) : ℕ) : ZMod (p i)) ≠ 0)
    (hasamples : ∀ i b, ((a b).values base).UnitsAt (p i))
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, ∑ x : ZMod (p i), ‖g i x‖ ^ 2 ≤ (p i : ℝ))
    (twist : ∀ i, Bool → (ZMod (p i))ˣ)
    (outside : List ℕ) (childBound : ℕ → ℕ) (input : PublishedProgressionInput) (Qfreq Qbulk : ℕ)
    (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (Ybulk : TreeLeafIndex n × Fin m → ℝ) (hYbulk : ∀ j, 0 ≤ Ybulk j) :
    let ts := fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)
    let T := fun b => buildMovingSlotData n (ts b) (small b) (bulkSlotLeaves n m slot) (a b)
    let Freq := frozenBulkFrequencyPrime base slot outside F E T childBound R
      (R ^ (n - 1 + 2)) input Qfreq X Y
    let Spec := fun i => frozenBulkSpectatorPrime base n m ts small a (twist i) (Equiv.refl _) (g i)
    (Fintype.card (TreeLeafIndex n × Fin m →
      (ZMod (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i))ˣ) : ℝ)⁻¹ *
      (∑ x : TreeLeafIndex n × Fin m →
          (ZMod (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i))ˣ,
        ‖(Freq (bulkResidueEquiv (R ^ (n - 1 + 2)) p hc x).1 *
          ∏ j, pageGiantWeight input Qbulk (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)
            (x j).val.val (Ybulk j)) *
          ∏ i, Spec i ((bulkResidueEquiv (R ^ (n - 1 + 2)) p hc x).2 i)‖) ≤
      (2 : ℝ) ^ (2 ^ n * m) *
        ((4 * ((‖movingDataWeight (F false) (E false) (T false)‖ *
          ‖movingDataWeight (F true) (E true) (T true)‖) *
          ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod)) *
        (3 : ℝ) ^ (2 ^ n * Fintype.card I)) := by
  intro ts T Freq Spec
  let B := 4 * ((‖movingDataWeight (F false) (E false) (T false)‖ *
    ‖movingDataWeight (F true) (E true) (T true)‖) *
    ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod)
  have hprob : 0 ≤ ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod := by
    apply List.prod_nonneg
    intro c hc
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hc
    exact pairFrequencySupportBound_nonneg D f
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hFreq : (Fintype.card (TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ) : ℝ)⁻¹ *
      ∑ z, ‖Freq z‖ ≤ B :=
    frozenBulkFrequencyPrime_mean_le base tier S n m R t hS hR slot small a hslot hsmall ha
      hbase F E N D hD hN hdiv hm outside childBound input Qfreq X Y hX hY
  have hSpec (i : I) : (Fintype.card (TreeLeafIndex n × Fin m → (ZMod (p i))ˣ) : ℝ)⁻¹ *
      ∑ z, ‖Spec i z‖ ≤ (3 : ℝ) ^ (2 ^ n) :=
    frozenBulkSpectatorPrime_absolute_mean_le (hp i) base n m hm ts small a
      (hfreq i) (hsmallp i) (hasamples i) (twist i) (Equiv.refl _) (g i) (hg i) (henergy i)
  have h := bulk_residue_absolute_mean_le (I := I) (J := TreeLeafIndex n × Fin m)
    (R ^ (n - 1 + 2)) p hc input Qbulk Ybulk hYbulk
    Freq Spec B hB (fun _ => (3 : ℝ) ^ (2 ^ n))
    (by
      simp only [finite_univ_canonical, Fintype.card_eq_nat_card] at hFreq ⊢
      exact hFreq)
    (by
      intro i
      have hi := hSpec i
      simp only [finite_univ_canonical, Fintype.card_eq_nat_card] at hi ⊢
      exact hi)
  simp only [Fintype.card_prod, card_treeLeafIndex, Fintype.card_fin, Finset.prod_const,
    Finset.card_univ, ← pow_mul, B] at h
  simp only [finite_univ_canonical, Fintype.card_eq_nat_card] at h ⊢
  exact h

end
end Ostmann

end OAI
