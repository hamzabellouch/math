import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportedOuterFactor
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterCoprimeComparison

namespace OAI

/-! # Corrected Haar comparison for the literal fully supported history pair -/

namespace Ostmann
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_original_supported_prime_haar_rate (P : PublishedProgressionInput)
    {σ I : Type*} (p : I → ℕ) [∀ i, Fact (p i).Prime] (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (tier : σ → ℕ) (value : σ → ℕ)
      (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
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
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q : ℕ, 2 ≤ Q → ∀ hq : 1 ≤ q, q ≤ Q →
      q = movingFullPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf p S →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
      let c := movingFullPairResidueCoefficient p value outside F E g Dq S T nodes
      ∀ A : ℝ, 0 ≤ A → (∀ a < q, ∀ b < q, ‖c a b‖ ≤ A) →
      2 * (A * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      letI : NeZero q := ⟨by omega⟩
      ‖complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun x =>
          movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
            Jleft Jright diagonal T t ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y) *
            correctedPrimePairAverage P Q q c x y / ((x : ℂ) * (y : ℂ)))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [(P.moving_outer_coprime_prime_haar_rate n C d).mono (fun _ h => h σ)] with L hL
  intro tier value hprime hdisjoint outside childBound pivotBound T hf t hT hlevels hcoh hc hsmall hfmod
    F E g hg Dq S ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal V hV
    Q q hQ hq hqQ hqeq hlog u v r s hu huv hshort hr hrs hrshort hqlog
  dsimp only
  intro A hA0 hA hbudget
  let hv := fun i => (hprime i).ne_zero
  let nodes := fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true)
  let c := movingFullPairResidueCoefficient p value outside F E g Dq S T nodes
  have h := hL value hv childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
    diagonal V hV Q q hQ hq hqQ hlog u v r s hu huv hshort hr hrs hrshort hqlog c A hA0 hA hbudget
  dsimp only at h
  have hfactor (x y : ℕ) :
      movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
        Jleft Jright diagonal T t x y =
      if x.Coprime y then c (x % q) (y % q) *
        movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal x y else 0 := by
    rw [hqeq]
    exact movingOriginalSupportedOuterPair_factor p tier value hprime hdisjoint outside childBound pivotBound
      F E g hg Dq S ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal
      T t hT hf hlevels hcoh hc hsmall hfmod x y
  simpa only [hfactor] using h

theorem PublishedProgressionInput.moving_original_supported_mixed_haar_rate (P : PublishedProgressionInput)
    {σ I : Type*} (p : I → ℕ) [∀ i, Fact (p i).Prime] (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (tier : σ → ℕ) (value : σ → ℕ)
      (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
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
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q : ℕ, 2 ≤ Q → ∀ hq : 1 ≤ q, q ≤ Q →
      q = movingFullPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf p S →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
      let c := movingFullPairResidueCoefficient p value outside F E g Dq S T nodes
      ∀ A : ℝ, 0 ≤ A → (∀ a < q, ∀ b < q, ‖c a b‖ ≤ A) →
      2 * (A * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      letI : NeZero q := ⟨by omega⟩
      ‖complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
          movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
            Jleft Jright diagonal T t ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y) *
            (Real.exp (x - J) : ℂ) * correctedMixedPairAverage P Q q c y / (y : ℂ))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [(P.moving_outer_coprime_mixed_haar_rate n C d).mono (fun _ h => h σ)] with L hL
  intro tier value hprime hdisjoint outside childBound pivotBound T hf t hT hlevels hcoh hc hsmall hfmod
    F E g hg Dq S ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal V hV
    Q q hQ hq hqQ hqeq hlog u v r s J hJ huv hshort hvJ hr hrs hrshort hqlog
  dsimp only
  intro A hA0 hA hbudget
  let hv := fun i => (hprime i).ne_zero
  let nodes := fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true)
  let c := movingFullPairResidueCoefficient p value outside F E g Dq S T nodes
  have h := hL value hv childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
    diagonal V hV Q q hQ hq hqQ hlog u v r s J hJ huv hshort hvJ hr hrs hrshort hqlog c A hA0 hA hbudget
  dsimp only at h
  have hfactor (x y : ℕ) :
      movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
        Jleft Jright diagonal T t x y =
      if x.Coprime y then c (x % q) (y % q) *
        movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal x y else 0 := by
    rw [hqeq]
    exact movingOriginalSupportedOuterPair_factor p tier value hprime hdisjoint outside childBound pivotBound
      F E g hg Dq S ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal
      T t hT hf hlevels hcoh hc hsmall hfmod x y
  simpa only [hfactor] using h

end Ostmann

end OAI
