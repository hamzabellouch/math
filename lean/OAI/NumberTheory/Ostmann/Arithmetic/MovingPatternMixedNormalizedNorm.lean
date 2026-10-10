import OAI.NumberTheory.Ostmann.Arithmetic.FrozenBulkFrequencyNorm
import OAI.NumberTheory.Ostmann.Arithmetic.BulkResidueAbsolute

import OAI.NumberTheory.Ostmann.Arithmetic.FrozenUnitArithmetic
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternSpectatorUnits
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkFrozen
import OAI.NumberTheory.Ostmann.Characters.NormalizedResidueIndicator

namespace OAI

/-! # Mixed arithmetic norm with distinct giant and bulk Page cutoffs -/

namespace Ostmann
open scoped Classical BigOperators

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
theorem frozenArithmetic_same_assignment_mixed_norm
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
    (Y : ℝ) (hY : 0 ≤ Y) (Ybulk : TreeLeafIndex n × Fin m → ℝ) (hYbulk : ∀ j, 0 ≤ Ybulk j) :
    let ts := fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)
    let T := fun b => buildMovingSlotData n (ts b) (small b) (bulkSlotLeaves n m slot) (a b)
    let Freq := frozenBulkFrequencyFactor base slot outside F E T childBound R
      (R ^ (n - 1 + 2)) input Qfreq Y
    let Spec := fun i => frozenBulkSpectatorHaar base n m ts small a (twist i) (Equiv.refl _) (g i)
    (Fintype.card (TreeLeafIndex n × Fin m →
      (ZMod (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i))ˣ) : ℝ)⁻¹ *
      (∑ x : TreeLeafIndex n × Fin m →
          (ZMod (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i))ˣ,
        ‖(Freq (bulkResidueEquiv (R ^ (n - 1 + 2)) p hc x).1 *
          ∏ j, pageGiantWeight input Qbulk (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)
            (x j).val.val (Ybulk j)) *
          ∏ i, Spec i ((bulkResidueEquiv (R ^ (n - 1 + 2)) p hc x).2 i)‖) ≤
      (2 : ℝ) ^ (2 ^ n * m) *
        ((2 * ((‖movingDataWeight (F false) (E false) (T false)‖ *
          ‖movingDataWeight (F true) (E true) (T true)‖) *
          ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod)) *
        (3 : ℝ) ^ (2 ^ n * Fintype.card I)) := by
  intro ts T Freq Spec
  let B := 2 * ((‖movingDataWeight (F false) (E false) (T false)‖ *
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
    frozenBulkFrequencyFactor_mean_le base tier S n m R t hS hR slot small a hslot hsmall ha
      hbase F E N D hD hN hdiv hm outside childBound input Qfreq Y hY
  have hSpec (i : I) : (Fintype.card (TreeLeafIndex n × Fin m → (ZMod (p i))ˣ) : ℝ)⁻¹ *
      ∑ z, ‖Spec i z‖ ≤ (3 : ℝ) ^ (2 ^ n) :=
    frozenBulkSpectatorHaar_absolute_mean_le (hp i) base n m hm ts small a
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

noncomputable def frozenMixedUnitArithmeticMean {σ I : Type*} [Fintype I]
    (base : σ → ℕ) (n m R : ℕ) [NeZero (R ^ (n - 1 + 2))]
    (ts : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List σ) n)
    (a : Bool → MovingSampleSlots σ n) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (outside : List ℕ) (childBound : ℕ → ℕ) (input : PublishedProgressionInput) (Qfreq Qbulk : ℕ)
    (Y : ℝ) (p : I → ℕ) [∀ i, Fact (p i).Prime]
    [NeZero (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli (R ^ (n - 1 + 2)) p i).Coprime
      (bulkResidueModuli (R ^ (n - 1 + 2)) p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (twist : ∀ i, Bool → (ZMod (p i))ˣ)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) : ℝ :=
  let T := fun b => buildMovingSlotData n (ts b) (small b) (bulkSlotLeaves n m slot) (a b)
  let Freq := frozenBulkFrequencyFactor base slot outside F (fun _ _ _ _ _ => 1) T childBound R
    (R ^ (n - 1 + 2)) input Qfreq Y
  let Spec := fun i => frozenBulkSpectatorHaar base n m ts small a (twist i) (Equiv.refl _) (g i)
  (Fintype.card (TreeLeafIndex n × Fin m →
    (ZMod (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i))ˣ) : ℝ)⁻¹ *
    ∑ x : TreeLeafIndex n × Fin m → (ZMod (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i))ˣ,
      ‖(Freq (bulkResidueEquiv (R ^ (n - 1 + 2)) p hc x).1 *
        ∏ j, pageGiantWeight input Qbulk (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)
          (x j).val.val (Ybulk j)) *
        ∏ i, Spec i ((bulkResidueEquiv (R ^ (n - 1 + 2)) p hc x).2 i)‖

theorem frozenMixedUnitArithmeticMean_nonneg {σ I : Type*} [Fintype I]
    (base : σ → ℕ) (n m R : ℕ) [NeZero (R ^ (n - 1 + 2))]
    (ts : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List σ) n)
    (a : Bool → MovingSampleSlots σ n) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (outside : List ℕ) (childBound : ℕ → ℕ) (input : PublishedProgressionInput) (Qfreq Qbulk : ℕ)
    (Y : ℝ) (p : I → ℕ) [∀ i, Fact (p i).Prime]
    [NeZero (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli (R ^ (n - 1 + 2)) p i).Coprime
      (bulkResidueModuli (R ^ (n - 1 + 2)) p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (twist : ∀ i, Bool → (ZMod (p i))ˣ)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) :
    0 ≤ frozenMixedUnitArithmeticMean base n m R ts small a slot F outside childBound input Qfreq Qbulk Y
      p hc g twist Ybulk := by unfold frozenMixedUnitArithmeticMean; positivity

theorem frozenMixedUnitArithmeticMean_le {σ I : Type*} [Fintype I]
    (base : σ → ℕ) (tier : σ → ℕ) (S : Finset ℤ) (n m R N V : ℕ)
    [NeZero (R ^ (n - 1 + 2))] (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) (hN : ∀ s ∈ S, s.natAbs ≤ N)
    (hR : ∀ b (j : Fin (2 ^ n - 1)),
      (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
    (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n)
    (hslot : ∀ j, n ≤ tier (slot j))
    (hsmall : ∀ b i, i ∈ flattenMovingSlots n (small b) → i ∉ Set.range slot)
    (ha : ∀ b, (a b).Levels tier)
    (hbase : ∀ i ∉ Set.range slot, IsCoprime (base i : ℤ) (R : ℤ))
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (hF : ∀ b s regular, ‖F b (.leaf s regular) s‖ ≤ if s.natAbs ≤ V then 1 else 0)
    (D : ℝ) (hD : 0 ≤ D)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D) (hm : 0 < m)
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    [NeZero (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli (R ^ (n - 1 + 2)) p i).Coprime
      (bulkResidueModuli (R ^ (n - 1 + 2)) p j))) (hp : ∀ i, 3 ≤ p i)
    (hfreq : ∀ i b, movingGiantFrequencyUnits (p i) n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)))
    (hsmallp : ∀ i b, ((treeLeafProduct n (movingSlotValues base n (small b)) : ℕ) : ZMod (p i)) ≠ 0)
    (hasamples : ∀ i b, ((a b).values base).UnitsAt (p i))
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, ∑ x : ZMod (p i), ‖g i x‖ ^ 2 ≤ (p i : ℝ))
    (twist : ∀ i, Bool → (ZMod (p i))ˣ) (outside : List ℕ) (childBound : ℕ → ℕ)
    (input : PublishedProgressionInput) (Qfreq Qbulk : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) (hYbulk : ∀ j, 0 ≤ Ybulk j) :
    frozenMixedUnitArithmeticMean base n m R
      (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      small a slot F outside childBound input Qfreq Qbulk Y p hc g twist Ybulk ≤
      ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * Fintype.card I)) *
        (frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
          ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) := by
  have h := frozenArithmetic_same_assignment_mixed_norm base tier S n m R t hS hR slot small a
    hslot hsmall ha hbase F (fun _ _ _ _ _ => 1) N D hD hN hdiv hm p hc hp hfreq
    hsmallp hasamples g hg henergy twist outside childBound input Qfreq Qbulk Y hY Ybulk hYbulk
  have hamp := movingDataWeight_pair_unit_leaf_bound F V hF S n t small (bulkSlotLeaves n m slot) a
  have hprob : 0 ≤ ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod := by
    apply List.prod_nonneg
    intro c hc
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hc
    exact pairFrequencySupportBound_nonneg D f
  have hbound := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hamp hprob) (by norm_num : (0 : ℝ) ≤ 2))
      (by positivity : (0 : ℝ) ≤ 3 ^ (2 ^ n * Fintype.card I)))
    (by positivity : (0 : ℝ) ≤ 2 ^ (2 ^ n * m))
  have h' : frozenMixedUnitArithmeticMean base n m R
      (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      small a slot F outside childBound input Qfreq Qbulk Y p hc g twist Ybulk ≤ _ := h
  exact h'.trans (hbound.trans_eq (by ring))

theorem movingPattern_same_assignment_mixed_norm {B C I : Type*} [Fintype I] {N₀ n m : ℕ}
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
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, ∑ x : ZMod (p i), ‖g i x‖ ^ 2 ≤ (p i : ℝ))
    (twist : ∀ i, Bool → (ZMod (p i))ˣ) (outside : List ℕ) (childBound : ℕ → ℕ)
    (input : PublishedProgressionInput) (Qfreq Qbulk : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) (hYbulk : ∀ j, 0 ≤ Ybulk j) :
    let ts := fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)
    let data := movingPatternFinBulkData e n m ts small slot (Equiv.refl _) pattern
    let freq := frozenBulkFrequencyFactor base (movingPatternBulkEmbedding e slot) outside
      F (fun _ _ _ _ _ => 1) data childBound R (R ^ (n - 1 + 2)) input Qfreq Y
    let spec := fun i => frozenBulkSpectatorHaar base n m ts
      (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
      (twist i) (Equiv.refl _) (g i)
    let M := ∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i
    let A := fun z => freq (bulkResidueEquiv (R ^ (n - 1 + 2)) p hc z).1 *
      ∏ i, spec i ((bulkResidueEquiv (R ^ (n - 1 + 2)) p hc z).2 i)
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod M)ˣ) : ℝ)⁻¹ *
      (∑ z : TreeLeafIndex n × Fin m → (ZMod M)ˣ,
        ‖A z * ∏ j, pageGiantWeight input Qbulk M (z j).val.val (Ybulk j)‖) ≤
      ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * Fintype.card I)) *
        (frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
          ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) := by
  intro ts data freq spec M A
  have hslot (j : TreeLeafIndex n × Fin m) :
      n ≤ ((Sum.elim tierB tierC) ∘ e) (movingPatternBulkEmbedding e slot j) := by
    change n ≤ Sum.elim tierB tierC (e (e.symm (.inl (slot j))))
    simpa only [Equiv.apply_symm_apply, Sum.elim_inl] using hB (slot j)
  have hd : data = fun b => buildMovingSlotData n (ts b) (movingPatternFiniteSmall e n (small b))
      (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot)) (movingPatternFiniteSamples e n pattern b) := by
    funext b
    dsimp only [data]
    rw [movingPatternFinBulkData_build]
    cases b <;> rfl
  have h := frozenMixedUnitArithmeticMean_le base ((Sum.elim tierB tierC) ∘ e) S n m R N V t
    hS hN hR (movingPatternBulkEmbedding e slot) (fun b => movingPatternFiniteSmall e n (small b))
    (movingPatternFiniteSamples e n pattern) hslot
    (fun b => movingPatternFiniteSmall_absent e slot (small b) (hsmall b))
    (movingPatternFiniteSamples_levels e tierB tierC n pattern htier) hbase F hF D hD hdiv hm p hc hp hfreq
    (fun i b => movingPatternFiniteSmall_unit e base (small b) (hsmallp i b))
    (fun i => movingPatternFiniteSamples_units e base pattern (hasamples i))
    g hg henergy twist outside childBound input Qfreq Qbulk Y hY Ybulk hYbulk
  dsimp only [A, freq, spec, M]
  rw [hd]
  unfold frozenMixedUnitArithmeticMean at h
  dsimp only at h
  simp only [finite_univ_canonical, Fintype.card_eq_nat_card] at h ⊢
  apply le_trans (le_of_eq ?_) h
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  exact mul_right_comm _ _ _

theorem movingPattern_normalized_same_assignment_mixed_norm {B C I : Type*} [Fintype I] {N₀ n m : ℕ}
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
    (input : PublishedProgressionInput) (Qfreq Qbulk : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) (hYbulk : ∀ j, 0 ≤ Ybulk j) :
    let ts := fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)
    let data := movingPatternFinBulkData e n m ts small slot (Equiv.refl _) pattern
    let freq := frozenBulkFrequencyFactor base (movingPatternBulkEmbedding e slot) outside
      F (fun _ _ _ _ _ => 1) data childBound R (R ^ (n - 1 + 2)) input Qfreq Y
    let spec := fun i => frozenBulkSpectatorHaar base n m ts
      (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
      (twist i) (Equiv.refl _) (normalizedResidueTransform (sets i))
    let M := ∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i
    let A := fun z => freq (bulkResidueEquiv (R ^ (n - 1 + 2)) p hc z).1 *
      ∏ i, spec i ((bulkResidueEquiv (R ^ (n - 1 + 2)) p hc z).2 i)
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod M)ˣ) : ℝ)⁻¹ *
      (∑ z : TreeLeafIndex n × Fin m → (ZMod M)ˣ,
        ‖A z * ∏ j, pageGiantWeight input Qbulk M (z j).val.val (Ybulk j)‖) ≤
      ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * Fintype.card I)) *
        (frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
          ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) := by
  exact movingPattern_same_assignment_mixed_norm e tierB tierC S t R N V hS hN hR small slot pattern
    hsmall hB htier base hbase F hF D hD hdiv hm p hc hp hfreq hsmallp hasamples
    (fun i => normalizedResidueTransform (sets i))
    (fun i => normalizedResidueTransform_zero (sets i))
    (fun i => (normalizedResidueTransform_energy (sets i) (hsets i) (hsetsLt i)).le)
    twist outside childBound input Qfreq Qbulk Y hY Ybulk hYbulk

end Ostmann

end OAI
