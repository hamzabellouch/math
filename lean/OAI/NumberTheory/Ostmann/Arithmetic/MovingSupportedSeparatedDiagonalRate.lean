import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedDiagonalRate
import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompensationSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterVariationScale
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedRegularNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantBounds

namespace OAI

/-! # Numerical giant comparison for the original diagonal -/

namespace Ostmann
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_original_supported_separated_diagonal_prime_rate (P : PublishedProgressionInput)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (Afreq Wwin B D : ℝ)
    (hAfreq : 0 ≤ Afreq) (hWwin : 0 ≤ Wwin) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (σ J : Type) [Fintype J] (p : Fin m → ℕ) [∀ i, Fact (p i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
      (hprime : ∀ i, (value i).Prime) (_hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
      (outside : List ℕ)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (t : Bool → FrequencyTree ℤ n) (_hT : ∀ b, (T b).Follows (t b))
      (_hlevels : ∀ b, (T b).Levels tier) (_hcoh : ∀ b, (T b).RegularCoherent)
      (_hsmall : ∀ b i, (T b).Frequencies (fun s => IsCoprime s (value i : ℤ)))
      (_hfmod : ∀ b i, (T b).Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
      (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
      (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
      (g : ∀ i, ZMod (p i) → ℂ) (_hg : ∀ i, g i 0 = 0)
      (Dq : Bool → ∀ i, (ZMod (p i))ˣ)
      (R : ℤ) (_hR : ∀ b, (T b).frequencyProduct ∣ R)
      (_hsmallR : ∀ i, IsCoprime (value i : ℤ) R)
      (_hden : ∀ b i, (T b).ModularDenominators value (p i))
      (_hcover : ∀ q ∈ outside, ∃ i, p i = q)
      (reg : J → ℕ) [∀ i, Fact (reg i).Prime]
      (_hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = ∏ i, reg i)
      (active : J → Bool) (sreg : ℤ) (other : ∀ i, ZMod (reg i)) (greg : ∀ i, ZMod (reg i) → ℂ)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright : ℝ)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      0 ≤ V → V ≤ Real.exp (Afreq * m) → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      ∀ M : ℕ, ∀ _hM : NeZero M,
      R ^ (n + 1) ∣ (M : ℤ) →
      (∀ b, ∀ o ∈ (T b).occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ (M : ℤ)) →
      (∀ i, (p i : ℤ) ∣ (M : ℤ)) → (∏ i, reg i).Coprime M →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, q ≤ giantProgressionCutoff L →
      ∀ hqeq : q = (∏ i, reg i) * M,
      (∀ b, movingRegularOutsidePairwise value outside (T b)) →
      Pairwise (fun i j => (reg i).Coprime (reg j)) →
      (∀ i, (∏ j, reg j).Coprime (p i)) →
      pageAtModulus q (selectedPageZero P (giantProgressionCutoff L)) =
        pageAtModulus (M) (selectedPageZero P (giantProgressionCutoff L)) →
      (∀ i, (sreg : ZMod (reg i)) ≠ 0) → (∀ i, other i ≠ 0) →
      (∀ i, greg i 0 = 0) → (∀ i, (∑ x : ZMod (reg i), ‖greg i x‖ ^ 2) = reg i) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      (∀ b, ‖movingDataWeight (F b) (E b) (T b)‖ ≤ 1) →
      (∀ i z, ‖g i z‖ ≤ p i) →
      let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
      let c0 := movingSeparatedPairResidueCoefficient p value outside F E g Dq Finset.univ T nodes R
      let : NeZero q := ⟨by omega⟩
      let : NeZero (M) := ⟨by
        intro hz
        rw [hz, mul_zero] at hqeq
        omega⟩
      ‖complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
          movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq Finset.univ ψ X lo hi φ G
            Jleft Jright diagonal T t ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ *
              (naturalRegularMultiplier reg active sreg other greg ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ : ℂ))) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y) *
            (Real.exp (x - J) : ℂ) * (((∏ i, if active i then (1 : ℝ) else 1 - (reg i : ℝ)⁻¹ : ℝ) : ℂ) *
              correctedMixedPairAverage P (giantProgressionCutoff L) (M) c0 y) / (y : ℂ))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_original_separated_diagonal_prime_rate ψ n r₀ k Afreq Wwin B D
    hAfreq hWwin hB hD] with L hrate
  dsimp only
  intro σ J _ p _ tier value hprime hdisjoint outside childBound pivotBound T hf t hT
    hlevels hcoh hsmall hfmod F E g hg Dq R hR hsmallR hden hcover reg _ hregular active sreg other greg
    X lo hi hlo hhi φ G Jleft Jright hφ hlip hout diagonal V hV hV0 hVA hwindow hpupper
    M hM hfrequency hsquare hspectator hcop q hq hqQ hqeq houtside hreg hqs hpage hsreg hother hgreg henergy
    u v r s H hH huv hshort hvH hr hrs hrshort hweight hgnorm
  by_cases hd : ∀ b, (T b).CompensationDistinct value
  · have hc : ∀ b, (T b).CompensationPrimeData value := fun b =>
      (T b).compensationPrimeData_of_units value hprime (hsmall b) (hd b)
    exact hrate σ J p tier value hprime hdisjoint outside childBound pivotBound T hf t hT
      hlevels hcoh hc hsmall hfmod F E g hg Dq R hR hsmallR hden hcover reg hregular active sreg other greg
      X lo hi hlo hhi φ G Jleft Jright hφ hlip hout diagonal V hV hV0 hVA hwindow hpupper
      M hM hfrequency hsquare hspectator hcop q hq hqQ hqeq houtside hreg hqs hpage
      hsreg hother hgreg henergy u v r s H hH huv hshort hvH hr hrs hrshort hweight hgnorm
  · obtain ⟨b, hb⟩ := not_forall.mp hd
    have horiginal (XL XR : ℕ) :
        movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq Finset.univ
          ψ X lo hi φ G Jleft Jright diagonal T t XL XR = 0 := by
      have hz := movingSupportedWeight_zero_of_compensation_collision value outside
        (T b) (hcoh b) hb XL XR
      cases b <;> simp only [movingOriginalSupportedOuterPair, hz, map_zero, zero_mul, mul_zero]
    have hsep (nodes : Bool → List MovingFormulaNode) (a b' : ℕ) :
        movingSeparatedPairResidueCoefficient p value outside F E g Dq Finset.univ T nodes R a b' = 0 := by
      have hz := movingSeparatedResidueCoefficient_zero_of_compensation_collision p value outside
        (F b) (E b) g (Dq b) Finset.univ (T b) (nodes b) R a b' (hcoh b) hb
      cases b <;> simp only [movingSeparatedPairResidueCoefficient, hz, map_zero, zero_mul, mul_zero]
    simp [horiginal, hsep, correctedMixedPairAverage, complexPrimeInterval, complexIntegerInterval]
    positivity

end Ostmann

end OAI
