import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedSupportedPair
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPairCoprimeComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompensationSupport

namespace OAI

/-! # The original prime-pair Haar comparison at the separated frequency/internal/spectator modulus -/

namespace Ostmann
universe u v
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_original_supported_pair_haar_rate_uniform (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (I : Type v) (p : I → ℕ) [∀ i, Fact (p i).Prime],
      ∀ (tier : σ → ℕ) (value : σ → ℕ)
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
      (Dq : Bool → ∀ i, (ZMod (p i))ˣ) (S : Finset I)
      (_hcover : ∀ q ∈ outside, ∃ i ∈ S, p i = q)
      (R : ℤ) (_hR : ∀ b, (T b).frequencyProduct ∣ R)
      (_hsmallR : ∀ i, IsCoprime (value i : ℤ) R)
      (_hden : ∀ b i, i ∈ S → (T b).ModularDenominators value (p i))
      (Reg : ℕ)
      (_hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = Reg)
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q : ℕ, 2 ≤ Q → ∀ hq : 1 ≤ q, q ≤ Q →
      R ^ (n + 1) ∣ (q : ℤ) →
      (∀ b, ∀ o ∈ (T b).occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ q) →
      (∀ i ∈ S, (p i : ℤ) ∣ q) →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      0 < Reg → Real.log (Reg : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
      let c := movingSeparatedPairResidueCoefficient p value outside F E g Dq S T nodes R
      ∀ A : ℝ, 0 ≤ A → (∀ a < q, ∀ b < q, ‖c a b‖ ≤ A) →
      2 * A * (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      letI : NeZero q := ⟨by omega⟩
      ‖complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun x =>
          movingOriginalSupportedPair p value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
            T t ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y) *
            correctedPrimePairAverage P Q q c x y / ((x : ℂ) * (y : ℂ)))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_pair_coprime_prime_haar_rate_uniform n C d,
    eventually_gt_atTop (0 : ℝ)] with L hL hL0
  intro σ I p _ tier value hprime hdisjoint outside childBound pivotBound T hf t hT hlevels hcoh hsmall hfmod
    F E g hg Dq S hcover R hR hsmallR hden Reg hregular ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout V hV
    Q q hQ hq hqQ hfrequency hsquare hspectator hlog u v r s hu huv hshort hr hrs hrshort hqlog hReg0 hReglog
  dsimp only
  intro A hA0 hA hbudget
  by_cases hd : ∀ b, (T b).CompensationDistinct value
  · have hc : ∀ b, (T b).CompensationPrimeData value := fun b =>
      (T b).compensationPrimeData_of_units value hprime (hsmall b) (hd b)
    let hv := fun i => (hprime i).ne_zero
    let nodes := fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true)
    let c := movingSeparatedPairResidueCoefficient p value outside F E g Dq S T nodes R
    let f := fun x y : ℕ => movingOriginalSupportedPair p value outside childBound pivotBound F E g Dq S
      ψ X lo hi φ G T t x y
    let f₀ := fun x y : ℕ => if x.Coprime y then c (x % q) (y % q) *
      movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G x y else 0
    have h := hL σ value hv childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
      V hV Q q hQ hq hqQ hlog u v r s hu huv hshort hr hrs hrshort hqlog c A hA0 hA hbudget
    dsimp only at h
    have hfactor (x : ℕ) (hx : x ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊) (hxp : x.Prime)
        (y : ℕ) (hy : y ∈ Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp s⌋₊) (hyp : y.Prime) : f x y = f₀ x y := by
      have hXL : x.Coprime Reg := hxp.coprime_iff_not_dvd.mpr (fun hd =>
        (not_le_of_gt (giant_interval_gt_modulus L hL0 Reg hReg0 hReglog u v hu x hx))
          (Nat.le_of_dvd hReg0 hd))
      have hXR : y.Coprime Reg := hyp.coprime_iff_not_dvd.mpr (fun hd =>
        (not_le_of_gt (giant_interval_gt_modulus L hL0 Reg hReg0 hReglog r s hr y hy))
          (Nat.le_of_dvd hReg0 hd))
      exact movingOriginalSupportedPair_separated_factor p tier value hprime hdisjoint outside
        childBound pivotBound F E g hg Dq S hcover ψ X lo hi hlo hhi φ G B D hB hD
        hφ hlip hout T t hT hf hlevels hcoh hc hsmall hfmod R hR hsmallR hden
        Reg hregular q hfrequency hsquare hspectator x y hXL hXR
    have heq : complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v
        (fun x => f ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) =
        complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v
        (fun x => f₀ ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) := by
      apply complexPrimeInterval_congr
      intro y hy hyp _
      rw [Real.exp_log (by exact_mod_cast hyp.pos), Nat.floor_natCast]
      apply complexPrimeInterval_congr
      intro x hx hxp _
      rw [Real.exp_log (by exact_mod_cast hxp.pos), Nat.floor_natCast]
      exact hfactor x hx hxp y hy hyp
    change ‖complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v
      (fun x => f ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) - _‖ ≤ _
    rw [heq]
    exact h
  · obtain ⟨b, hb⟩ := not_forall.mp hd
    have horiginal (XL XR : ℕ) :
        movingOriginalSupportedPair p value outside childBound pivotBound F E g Dq S
          ψ X lo hi φ G T t XL XR = 0 := by
      have hz := movingSupportedWeight_zero_of_compensation_collision value outside
        (T b) (hcoh b) hb XL XR
      cases b <;> simp only [movingOriginalSupportedPair, hz, map_zero, zero_mul, mul_zero]
    have hsep (nodes : Bool → List MovingFormulaNode) (a b' : ℕ) :
        movingSeparatedPairResidueCoefficient p value outside F E g Dq S T nodes R a b' = 0 := by
      have hz := movingSeparatedResidueCoefficient_zero_of_compensation_collision p value outside
        (F b) (E b) g (Dq b) S (T b) (nodes b) R a b' (hcoh b) hb
      cases b <;> simp only [movingSeparatedPairResidueCoefficient, hz, map_zero, zero_mul, mul_zero]
    simp [horiginal, hsep, correctedPrimePairAverage, complexPrimeInterval]
    positivity

theorem PublishedProgressionInput.moving_original_supported_pair_haar_rate (P : PublishedProgressionInput)
    {σ : Type u} {I : Type v} (p : I → ℕ) [∀ i, Fact (p i).Prime] (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (tier : σ → ℕ) (value : σ → ℕ)
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
      (Dq : Bool → ∀ i, (ZMod (p i))ˣ) (S : Finset I)
      (_hcover : ∀ q ∈ outside, ∃ i ∈ S, p i = q)
      (R : ℤ) (_hR : ∀ b, (T b).frequencyProduct ∣ R)
      (_hsmallR : ∀ i, IsCoprime (value i : ℤ) R)
      (_hden : ∀ b i, i ∈ S → (T b).ModularDenominators value (p i))
      (Reg : ℕ)
      (_hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = Reg)
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q : ℕ, 2 ≤ Q → ∀ hq : 1 ≤ q, q ≤ Q →
      R ^ (n + 1) ∣ (q : ℤ) →
      (∀ b, ∀ o ∈ (T b).occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ q) →
      (∀ i ∈ S, (p i : ℤ) ∣ q) →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      0 < Reg → Real.log (Reg : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
      let c := movingSeparatedPairResidueCoefficient p value outside F E g Dq S T nodes R
      ∀ A : ℝ, 0 ≤ A → (∀ a < q, ∀ b < q, ‖c a b‖ ≤ A) →
      2 * A * (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      letI : NeZero q := ⟨by omega⟩
      ‖complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun x =>
          movingOriginalSupportedPair p value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
            T t ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y) *
            correctedPrimePairAverage P Q q c x y / ((x : ℂ) * (y : ℂ)))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_original_supported_pair_haar_rate_uniform n C d] with L hL
  exact hL σ I p

end Ostmann

end OAI
