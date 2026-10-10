import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedModulusFactor
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterCoprimeComparison

namespace OAI

/-! # The original-prior Haar comparison at the split regular/auxiliary modulus -/

namespace Ostmann
universe u v w
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_original_reduced_regular_prime_haar_rate (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (I : Type v) (J : Type w) [Fintype J]
      (p : I → ℕ) [∀ i, Fact (p i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
      (hprime : ∀ i, (value i).Prime) (_hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
      (outside : List ℕ)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (t : Bool → FrequencyTree ℤ n) (_hT : ∀ b, (T b).Follows (t b))
      (_hlevels : ∀ b, (T b).Levels tier) (_hcoh : ∀ b, (T b).RegularCoherent)
      (_hc : ∀ b, (T b).CompensationPrimeData value)
      (_hsmall : ∀ b i, (T b).Frequencies (fun s => IsCoprime s (value i : ℤ)))
      (_hfmod : ∀ b i, (T b).Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
      (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
      (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
      (g : ∀ i, ZMod (p i) → ℂ) (_hg : ∀ i, g i 0 = 0)
      (Dq : Bool → ∀ i, (ZMod (p i))ˣ) (S : Finset I)
      (reg : J → ℕ) [∀ i, Fact (reg i).Prime]
      (_hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = ∏ i, reg i)
      (active : J → Bool) (sreg : ℤ) (other : ∀ i, ZMod (reg i)) (greg : ∀ i, ZMod (reg i) → ℂ)
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q : ℕ, 2 ≤ Q → ∀ hq : 1 ≤ q, q ≤ Q →
      q = (∏ i, reg i) * movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf p S →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
      let c := fun a b => movingReducedPairResidueCoefficient p value outside F E g Dq S T nodes a b *
        (guardedRegularMultiplier reg active sreg other greg a b : ℂ)
      ∀ A : ℝ, 0 ≤ A → (∀ a < q, ∀ b < q, ‖c a b‖ ≤ A) →
      2 * (A * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      letI : NeZero q := ⟨by omega⟩
      ‖complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun x =>
          movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
            Jleft Jright diagonal T t ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ *
              (naturalRegularMultiplier reg active sreg other greg ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ : ℂ))) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y) *
            correctedPrimePairAverage P Q q c x y / ((x : ℂ) * (y : ℂ)))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_outer_coprime_prime_haar_rate n C d] with L hL
  intro σ I J _ p _
  have hL := hL σ
  intro tier value hprime hdisjoint outside childBound pivotBound T hf t hT hlevels hcoh hc hsmall hfmod
    F E g hg Dq S reg instReg hregular active sreg other greg ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal V hV
    Q q hQ hq hqQ hqeq hlog u v r s hu huv hshort hr hrs hrshort hqlog
  dsimp only
  intro A hA0 hA hbudget
  let hv := fun i => (hprime i).ne_zero
  let nodes := fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true)
  let c := fun a b => movingReducedPairResidueCoefficient p value outside F E g Dq S T nodes a b *
    (guardedRegularMultiplier reg active sreg other greg a b : ℂ)
  have h := hL value hv childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
    diagonal V hV Q q hQ hq hqQ hlog u v r s hu huv hshort hr hrs hrshort hqlog c A hA0 hA hbudget
  dsimp only at h
  have hfactor (x y : ℕ) :
      movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
        Jleft Jright diagonal T t x y *
        (naturalRegularMultiplier reg active sreg other greg x y : ℂ) =
      if x.Coprime y then c (x % q) (y % q) *
        movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal x y else 0 := by
    have hregM : ∀ i, reg i ∣ q := by
      intro i
      rw [hqeq]
      exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem reg (Finset.mem_univ i)) _
    exact movingOriginalSupportedReducedRegular_modulus_factor p tier value hprime hdisjoint outside
      childBound pivotBound F E g hg Dq S ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD
      hφ hlip hout diagonal T t hT hf hlevels hcoh hc hsmall hfmod reg hregular active sreg other greg
      q (by rw [hqeq]; exact dvd_mul_left _ _) hregM x y
  simpa only [hfactor] using h

theorem PublishedProgressionInput.moving_original_reduced_regular_mixed_haar_rate (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (I : Type v) (J : Type w) [Fintype J]
      (p : I → ℕ) [∀ i, Fact (p i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
      (hprime : ∀ i, (value i).Prime) (_hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
      (outside : List ℕ)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (t : Bool → FrequencyTree ℤ n) (_hT : ∀ b, (T b).Follows (t b))
      (_hlevels : ∀ b, (T b).Levels tier) (_hcoh : ∀ b, (T b).RegularCoherent)
      (_hc : ∀ b, (T b).CompensationPrimeData value)
      (_hsmall : ∀ b i, (T b).Frequencies (fun s => IsCoprime s (value i : ℤ)))
      (_hfmod : ∀ b i, (T b).Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
      (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
      (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
      (g : ∀ i, ZMod (p i) → ℂ) (_hg : ∀ i, g i 0 = 0)
      (Dq : Bool → ∀ i, (ZMod (p i))ˣ) (S : Finset I)
      (reg : J → ℕ) [∀ i, Fact (reg i).Prime]
      (_hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = ∏ i, reg i)
      (active : J → Bool) (sreg : ℤ) (other : ∀ i, ZMod (reg i)) (greg : ∀ i, ZMod (reg i) → ℂ)
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q : ℕ, 2 ≤ Q → ∀ hq : 1 ≤ q, q ≤ Q →
      q = (∏ i, reg i) * movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf p S →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
      let c := fun a b => movingReducedPairResidueCoefficient p value outside F E g Dq S T nodes a b *
        (guardedRegularMultiplier reg active sreg other greg a b : ℂ)
      ∀ A : ℝ, 0 ≤ A → (∀ a < q, ∀ b < q, ‖c a b‖ ≤ A) →
      2 * (A * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      letI : NeZero q := ⟨by omega⟩
      ‖complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
          movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
            Jleft Jright diagonal T t ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ *
              (naturalRegularMultiplier reg active sreg other greg ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ : ℂ))) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y) *
            (Real.exp (x - J) : ℂ) * correctedMixedPairAverage P Q q c y / (y : ℂ))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_outer_coprime_mixed_haar_rate n C d] with L hL
  intro σ I J _ p _
  have hL := hL σ
  intro tier value hprime hdisjoint outside childBound pivotBound T hf t hT hlevels hcoh hc hsmall hfmod
    F E g hg Dq S reg instReg hregular active sreg other greg ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal V hV
    Q q hQ hq hqQ hqeq hlog u v r s J hJ huv hshort hvJ hr hrs hrshort hqlog
  dsimp only
  intro A hA0 hA hbudget
  let hv := fun i => (hprime i).ne_zero
  let nodes := fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true)
  let c := fun a b => movingReducedPairResidueCoefficient p value outside F E g Dq S T nodes a b *
    (guardedRegularMultiplier reg active sreg other greg a b : ℂ)
  have h := hL value hv childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
    diagonal V hV Q q hQ hq hqQ hlog u v r s J hJ huv hshort hvJ hr hrs hrshort hqlog c A hA0 hA hbudget
  dsimp only at h
  have hfactor (x y : ℕ) :
      movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
        Jleft Jright diagonal T t x y *
        (naturalRegularMultiplier reg active sreg other greg x y : ℂ) =
      if x.Coprime y then c (x % q) (y % q) *
        movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal x y else 0 := by
    have hregM : ∀ i, reg i ∣ q := by
      intro i
      rw [hqeq]
      exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem reg (Finset.mem_univ i)) _
    exact movingOriginalSupportedReducedRegular_modulus_factor p tier value hprime hdisjoint outside
      childBound pivotBound F E g hg Dq S ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD
      hφ hlip hout diagonal T t hT hf hlevels hcoh hc hsmall hfmod reg hregular active sreg other greg
      q (by rw [hqeq]; exact dvd_mul_left _ _) hregM x y
  simpa only [hfactor] using h

end Ostmann

end OAI
