import OAI.NumberTheory.Ostmann.Arithmetic.FrozenArithmeticNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingLeafAmplitude
import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyModelModulus
import OAI.NumberTheory.Ostmann.Characters.FourierWindowDecay

namespace OAI

/-! # The arithmetic norm after the explicit compensation factors are removed -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def frozenUnitArithmeticMean {σ I : Type*} [Fintype I]
    (base : σ → ℕ) (n m R : ℕ) [NeZero (R ^ (n - 1 + 2))]
    (ts : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List σ) n)
    (a : Bool → MovingSampleSlots σ n) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (outside : List ℕ) (childBound : ℕ → ℕ) (input : PublishedProgressionInput) (Q : ℕ)
    (Y : ℝ) (p : I → ℕ) [∀ i, Fact (p i).Prime]
    [NeZero (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli (R ^ (n - 1 + 2)) p i).Coprime
      (bulkResidueModuli (R ^ (n - 1 + 2)) p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (twist : ∀ i, Bool → (ZMod (p i))ˣ)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) : ℝ :=
  let T := fun b => buildMovingSlotData n (ts b) (small b) (bulkSlotLeaves n m slot) (a b)
  let Freq := frozenBulkFrequencyFactor base slot outside F (fun _ _ _ _ _ => 1) T childBound R
    (R ^ (n - 1 + 2)) input Q Y
  let Spec := fun i => frozenBulkSpectatorHaar base n m ts small a (twist i) (Equiv.refl _) (g i)
  (Fintype.card (TreeLeafIndex n × Fin m →
    (ZMod (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i))ˣ) : ℝ)⁻¹ *
    ∑ x : TreeLeafIndex n × Fin m → (ZMod (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i))ˣ,
      ‖(Freq (bulkResidueEquiv (R ^ (n - 1 + 2)) p hc x).1 *
        ∏ j, pageGiantWeight input Q (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)
          (x j).val.val (Ybulk j)) *
        ∏ i, Spec i ((bulkResidueEquiv (R ^ (n - 1 + 2)) p hc x).2 i)‖

theorem frozenUnitArithmeticMean_nonneg {σ I : Type*} [Fintype I]
    (base : σ → ℕ) (n m R : ℕ) [NeZero (R ^ (n - 1 + 2))]
    (ts : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List σ) n)
    (a : Bool → MovingSampleSlots σ n) (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (outside : List ℕ) (childBound : ℕ → ℕ) (input : PublishedProgressionInput) (Q : ℕ)
    (Y : ℝ) (p : I → ℕ) [∀ i, Fact (p i).Prime]
    [NeZero (∏ i, bulkResidueModuli (R ^ (n - 1 + 2)) p i)]
    (hc : Pairwise (fun i j => (bulkResidueModuli (R ^ (n - 1 + 2)) p i).Coprime
      (bulkResidueModuli (R ^ (n - 1 + 2)) p j)))
    (g : ∀ i, ZMod (p i) → ℂ) (twist : ∀ i, Bool → (ZMod (p i))ˣ)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) :
    0 ≤ frozenUnitArithmeticMean base n m R ts small a slot F outside childBound input Q Y
      p hc g twist Ybulk := by unfold frozenUnitArithmeticMean; positivity

theorem frozenUnitArithmeticMean_le {σ I : Type*} [Fintype I]
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
    (input : PublishedProgressionInput) (Q : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) (hYbulk : ∀ j, 0 ≤ Ybulk j) :
    frozenUnitArithmeticMean base n m R
      (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      small a slot F outside childBound input Q Y p hc g twist Ybulk ≤
      ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * Fintype.card I)) *
        (frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
          ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) := by
  have h := frozenArithmetic_same_assignment_norm base tier S n m R t hS hR slot small a
    hslot hsmall ha hbase F (fun _ _ _ _ _ => 1) N D hD hN hdiv hm p hc hp hfreq
    hsmallp hasamples g hg henergy twist outside childBound input Q Y hY Ybulk hYbulk
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
  have h' : frozenUnitArithmeticMean base n m R
      (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      small a slot F outside childBound input Q Y p hc g twist Ybulk ≤ _ := h
  exact h'.trans (hbound.trans_eq (by ring))

theorem frozenUnitArithmeticMean_sum_le {σ I : Type*} [Fintype I]
    (base : σ → ℕ) (tier : σ → ℕ) (S : Finset ℤ) (n m N V : ℕ)
    (R : FrequencyTree (S × S) n → ℕ) [∀ t, NeZero (R t ^ (n - 1 + 2))]
    (hS : ∀ s ∈ S, s ≠ 0) (hN : ∀ s ∈ S, s.natAbs ≤ N)
    (hR : ∀ t b (j : Fin (2 ^ n - 1)),
      (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R t)
    (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n)
    (hslot : ∀ j, n ≤ tier (slot j))
    (hsmall : ∀ b i, i ∈ flattenMovingSlots n (small b) → i ∉ Set.range slot)
    (ha : ∀ b, (a b).Levels tier)
    (hbase : ∀ t i, i ∉ Set.range slot → IsCoprime (base i : ℤ) (R t : ℤ))
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (hF : ∀ b s regular, ‖F b (.leaf s regular) s‖ ≤ if s.natAbs ≤ V then 1 else 0)
    (D : ℝ) (hD : 0 ≤ D)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D) (hm : 0 < m)
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    [∀ t, NeZero (∏ i, bulkResidueModuli (R t ^ (n - 1 + 2)) p i)]
    (hc : ∀ t, Pairwise (fun i j => (bulkResidueModuli (R t ^ (n - 1 + 2)) p i).Coprime
      (bulkResidueModuli (R t ^ (n - 1 + 2)) p j))) (hp : ∀ i, 3 ≤ p i)
    (hfreq : ∀ t i b, movingGiantFrequencyUnits (p i) n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)))
    (hsmallp : ∀ i b, ((treeLeafProduct n (movingSlotValues base n (small b)) : ℕ) : ZMod (p i)) ≠ 0)
    (hasamples : ∀ i b, ((a b).values base).UnitsAt (p i))
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, ∑ x : ZMod (p i), ‖g i x‖ ^ 2 ≤ (p i : ℝ))
    (twist : ∀ i, Bool → (ZMod (p i))ˣ) (outside : List ℕ) (childBound : ℕ → ℕ)
    (input : PublishedProgressionInput) (Q : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) (hYbulk : ∀ j, 0 ≤ Ybulk j) :
    (∑ t : FrequencyTree (S × S) n, frozenUnitArithmeticMean base n m (R t)
      (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      small a slot F outside childBound input Q Y p (hc t) g twist Ybulk) ≤
      ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * Fintype.card I)) *
        ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) * (2 * (V : ℝ)) ^ (2 * 2 ^ n)) := by
  let C : ℝ := (2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * Fintype.card I)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ t : FrequencyTree (S × S) n, C *
        (frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
          ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) := by
      apply Finset.sum_le_sum
      intro t _
      exact frozenUnitArithmeticMean_le base tier S n m (R t) N V t hS hN (hR t)
        slot small a hslot hsmall ha (hbase t) F hF D hD hdiv hm p (hc t) hp (hfreq t)
        hsmallp hasamples g hg henergy twist outside childBound input Q Y hY Ybulk hYbulk
    _ = C * ∑ t : FrequencyTree (S × S) n,
        frequencyTreeWeight (pairedFrequencyKernel S D) (pairedFrequencyLeaf S V) n t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [frequencyTreeWeight_eq_splitList]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (arithmetic_frequency_tree_sum_le S N V D hD (fun s hs => ⟨hS s hs, hN s hs⟩)
        (gcd_frequency_divisor_bound S N D (fun s hs => ⟨hS s hs, hN s hs⟩) hdiv) n) hC

theorem frozenUnitArithmetic_kernel_sum_le {σ I : Type*} [Fintype I]
    (base : σ → ℕ) (tier : σ → ℕ) (S : Finset ℤ) (n m N V : ℕ)
    (R : FrequencyTree (S × S) n → ℕ) [∀ t, NeZero (R t ^ (n - 1 + 2))]
    (hS : ∀ s ∈ S, s ≠ 0) (hN : ∀ s ∈ S, s.natAbs ≤ N)
    (hR : ∀ t b (j : Fin (2 ^ n - 1)),
      (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R t)
    (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n)
    (hslot : ∀ j, n ≤ tier (slot j))
    (hsmall : ∀ b i, i ∈ flattenMovingSlots n (small b) → i ∉ Set.range slot)
    (ha : ∀ b, (a b).Levels tier)
    (hbase : ∀ t i, i ∉ Set.range slot → IsCoprime (base i : ℤ) (R t : ℤ))
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (hF : ∀ b s regular, ‖F b (.leaf s regular) s‖ ≤ if s.natAbs ≤ V then 1 else 0)
    (D : ℝ) (hD : 0 ≤ D)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D) (hm : 0 < m)
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    [∀ t, NeZero (∏ i, bulkResidueModuli (R t ^ (n - 1 + 2)) p i)]
    (hc : ∀ t, Pairwise (fun i j => (bulkResidueModuli (R t ^ (n - 1 + 2)) p i).Coprime
      (bulkResidueModuli (R t ^ (n - 1 + 2)) p j))) (hp : ∀ i, 3 ≤ p i)
    (hfreq : ∀ t i b, movingGiantFrequencyUnits (p i) n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t)))
    (hsmallp : ∀ i b, ((treeLeafProduct n (movingSlotValues base n (small b)) : ℕ) : ZMod (p i)) ≠ 0)
    (hasamples : ∀ i b, ((a b).values base).UnitsAt (p i))
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, ∑ x : ZMod (p i), ‖g i x‖ ^ 2 ≤ (p i : ℝ))
    (twist : ∀ i, Bool → (ZMod (p i))ˣ) (outside : List ℕ) (childBound : ℕ → ℕ)
    (input : PublishedProgressionInput) (Q : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (Ybulk : TreeLeafIndex n × Fin m → ℝ) (hYbulk : ∀ j, 0 ≤ Ybulk j)
    (value : σ → ℝ) (pivotBound : ℕ → ℕ) (ψ : 𝓢(ℝ, ℂ))
    (X Δ hi : ℝ) (hΔ : 0 ≤ Δ) (hhi : Real.exp Δ ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ : ℝ) (hBφ : 0 ≤ Bφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (L₀ R₀ : ℝ) :
    (∑ t : FrequencyTree (S × S) n,
      ‖realValueKernelPair value childBound pivotBound
        (fun b => buildMovingSlotData n
          (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
          (small b) (bulkSlotLeaves n m slot) (a b))
        ψ X (Real.exp Δ) hi (Real.one_le_exp hΔ) hhi φ G L₀ R₀‖ *
      frozenUnitArithmeticMean base n m (R t)
        (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
        small a slot F outside childBound input Q Y p (hc t) g twist Ybulk) ≤
      (((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * Bφ ^ (2 ^ n - 1)) ^ 2 *
        Real.exp (-(2 ^ n : ℕ) * Δ)) *
      (((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * Fintype.card I)) *
        ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) * (2 * (V : ℝ)) ^ (2 * 2 ^ n))) := by
  let A := fun t : FrequencyTree (S × S) n => frozenUnitArithmeticMean base n m (R t)
    (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
    small a slot F outside childBound input Q Y p (hc t) g twist Ybulk
  let K := ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * Bφ ^ (2 ^ n - 1)) ^ 2 *
    Real.exp (-(2 ^ n : ℕ) * Δ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  calc
    _ ≤ ∑ t : FrequencyTree (S × S) n, K * A t := by
      apply Finset.sum_le_sum
      intro t _
      exact mul_le_mul_of_nonneg_right
        (realValueKernelPair_norm_exp value childBound pivotBound _ ψ X Δ hi hΔ hhi φ G Bφ hBφ hφ L₀ R₀)
        (frozenUnitArithmeticMean_nonneg base n m (R t) _ small a slot F outside childBound input Q Y
          p (hc t) g twist Ybulk)
    _ = K * ∑ t : FrequencyTree (S × S) n, A t := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (frozenUnitArithmeticMean_sum_le base tier S n m N V R hS hN hR slot small a hslot hsmall ha hbase
        F hF D hD hdiv hm p hc hp hfreq hsmallp hasamples g hg henergy twist outside childBound input Q Y hY
        Ybulk hYbulk) hK

end Ostmann

end OAI
