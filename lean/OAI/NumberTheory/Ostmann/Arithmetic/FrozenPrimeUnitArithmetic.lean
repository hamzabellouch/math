import OAI.NumberTheory.Ostmann.Arithmetic.FrozenPrimeArithmeticNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingLeafAmplitude
import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyModelModulus
import OAI.NumberTheory.Ostmann.Characters.FourierWindowDecay

namespace OAI

/-! # The original two-prime arithmetic norm after removing compensation factors -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def frozenPrimeUnitArithmeticMean {σ I : Type*} [Fintype I]
    (base : σ → ℕ) (n m R : ℕ) [NeZero (R ^ (n - 1 + 2))]
    (ts : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List σ) n)
    (a : Bool → MovingSampleSlots σ n) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (outside : List ℕ) (childBound : ℕ → ℕ) (input : PublishedProgressionInput) (Qfreq Qbulk : ℕ)
    (X Y : ℝ) (p : I → ℕ) [∀ i, Fact (p i).Prime]
    [NeZero (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli (R ^ (n - 1 + 2)) p i).Coprime
      (bulkResidueModuli (R ^ (n - 1 + 2)) p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (twist : ∀ i, Bool → (ZMod (p i))ˣ)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) : ℝ :=
  let T := fun b => buildMovingSlotData n (ts b) (small b) (bulkSlotLeaves n m slot) (a b)
  let Freq := frozenBulkFrequencyPrime base slot outside F (fun _ _ _ _ _ => 1) T childBound R
    (R ^ (n - 1 + 2)) input Qfreq X Y
  let Spec := fun i => frozenBulkSpectatorPrime base n m ts small a (twist i) (Equiv.refl _) (g i)
  (Fintype.card (TreeLeafIndex n × Fin m →
    (ZMod (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i))ˣ) : ℝ)⁻¹ *
    ∑ x : TreeLeafIndex n × Fin m → (ZMod (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i))ˣ,
      ‖(Freq (bulkResidueEquiv (R ^ (n - 1 + 2)) p hc x).1 *
        ∏ j, pageGiantWeight input Qbulk (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)
          (x j).val.val (Ybulk j)) *
        ∏ i, Spec i ((bulkResidueEquiv (R ^ (n - 1 + 2)) p hc x).2 i)‖

theorem frozenPrimeUnitArithmeticMean_nonneg {σ I : Type*} [Fintype I]
    (base : σ → ℕ) (n m R : ℕ) [NeZero (R ^ (n - 1 + 2))]
    (ts : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List σ) n)
    (a : Bool → MovingSampleSlots σ n) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (outside : List ℕ) (childBound : ℕ → ℕ) (input : PublishedProgressionInput) (Qfreq Qbulk : ℕ)
    (X Y : ℝ) (p : I → ℕ) [∀ i, Fact (p i).Prime]
    [NeZero (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli (R ^ (n - 1 + 2)) p i).Coprime
      (bulkResidueModuli (R ^ (n - 1 + 2)) p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (twist : ∀ i, Bool → (ZMod (p i))ˣ)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) :
    0 ≤ frozenPrimeUnitArithmeticMean base n m R ts small a slot F outside childBound input Qfreq Qbulk X Y
      p hc g twist Ybulk := by unfold frozenPrimeUnitArithmeticMean; positivity

theorem frozenPrimeUnitArithmeticMean_le {σ I : Type*} [Fintype I]
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
    (input : PublishedProgressionInput) (Qfreq Qbulk : ℕ) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) (hYbulk : ∀ j, 0 ≤ Ybulk j) :
    frozenPrimeUnitArithmeticMean base n m R
      (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      small a slot F outside childBound input Qfreq Qbulk X Y p hc g twist Ybulk ≤
      ((2 : ℝ) ^ (2 ^ n * m) * 4 * 3 ^ (2 ^ n * Fintype.card I)) *
        (frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
          ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) := by
  have h := frozenArithmetic_same_assignment_prime_norm base tier S n m R t hS hR slot small a
    hslot hsmall ha hbase F (fun _ _ _ _ _ => 1) N D hD hN hdiv hm p hc hp hfreq
    hsmallp hasamples g hg henergy twist outside childBound input Qfreq Qbulk X Y hX hY Ybulk hYbulk
  have hamp := movingDataWeight_pair_unit_leaf_bound F V hF S n t small (bulkSlotLeaves n m slot) a
  have hprob : 0 ≤ ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod := by
    apply List.prod_nonneg
    intro c hc
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hc
    exact pairFrequencySupportBound_nonneg D f
  have hbound := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hamp hprob) (by norm_num : (0 : ℝ) ≤ 4))
      (by positivity : (0 : ℝ) ≤ 3 ^ (2 ^ n * Fintype.card I)))
    (by positivity : (0 : ℝ) ≤ 2 ^ (2 ^ n * m))
  have h' : frozenPrimeUnitArithmeticMean base n m R
      (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      small a slot F outside childBound input Qfreq Qbulk X Y p hc g twist Ybulk ≤ _ := h
  exact h'.trans (hbound.trans_eq (by ring))

end Ostmann

end OAI
