import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedOuterComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedPageAverage

namespace OAI

/-! # Original diagonal giant comparison after integrating the regular primes -/

namespace Ostmann
universe u v w
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_original_reduced_diagonal_haar_rate (P : PublishedProgressionInput)
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
      ∀ hqeq : q = (∏ i, reg i) * movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf p S,
      (∀ b, movingRegularOutsidePairwise value outside (T b)) →
      Pairwise (fun i j => (reg i).Coprime (reg j)) →
      (∀ i ∈ S, (∏ j, reg j).Coprime (p i)) →
      pageAtModulus q (selectedPageZero P Q) =
        pageAtModulus (movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf p S) (selectedPageZero P Q) →
      (∀ i, (sreg : ZMod (reg i)) ≠ 0) → (∀ i, other i ≠ 0) →
      (∀ i, greg i 0 = 0) → (∀ i, (∑ x : ZMod (reg i), ‖greg i x‖ ^ 2) = reg i) →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
      let c0 := movingReducedPairResidueCoefficient p value outside F E g Dq S T nodes
      let c := fun a b => movingReducedPairResidueCoefficient p value outside F E g Dq S T nodes a b *
        (guardedRegularMultiplier reg active sreg other greg a b : ℂ)
      ∀ A : ℝ, 0 ≤ A → (∀ a < q, ∀ b < q, ‖c a b‖ ≤ A) →
      2 * (A * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      letI : NeZero q := ⟨by omega⟩
      letI : NeZero (movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf p S) := ⟨by
        intro hz
        rw [hz, mul_zero] at hqeq
        omega⟩
      ‖complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
          movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
            Jleft Jright diagonal T t ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ *
              (naturalRegularMultiplier reg active sreg other greg ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ : ℂ))) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y) *
            (Real.exp (x - J) : ℂ) * (((∏ i, if active i then (1 : ℝ) else 1 - (reg i : ℝ)⁻¹ : ℝ) : ℂ) *
              correctedMixedPairAverage P Q (movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf p S) c0 y) / (y : ℂ))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_original_reduced_regular_mixed_haar_rate n C d] with L hL
  intro σ I J _ p _
  have hL := hL σ I J p
  intro tier value hprime hdisjoint outside childBound pivotBound T hf t hT hlevels hcoh hc hsmall hfmod
    F E g hg Dq S reg instReg hregular active sreg other greg ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal V hV
    Q q hQ hq hqQ hqeq houtside hreg hqs hpage hsreg hother hgreg henergy hlog
    u v r s J hJ huv hshort hvJ hr hrs hrshort hqlog
  dsimp only
  intro A hA0 hA hbudget
  let hv := fun i => (hprime i).ne_zero
  let R := movingReducedPairModulus value hv outside childBound pivotBound T hf p S
  let nodes := fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true)
  let c0 := movingReducedPairResidueCoefficient p value outside F E g Dq S T nodes
  let c := fun a b => c0 a b * (guardedRegularMultiplier reg active sreg other greg a b : ℂ)
  have : NeZero q := ⟨by omega⟩
  have : NeZero R := ⟨by
    intro hz
    have hzq : q = 0 := by rw [hqeq, show movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf p S = R from rfl, hz, mul_zero]
    omega⟩
  have : ∀ i, NeZero (reg i) := fun i => ⟨(Fact.out : (reg i).Prime).ne_zero⟩
  have : NeZero (∏ i, reg i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (Fact.out : (reg i).Prime).ne_zero)⟩
  have : NeZero ((∏ i, reg i) * R) := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hbase := hL tier value hprime hdisjoint outside childBound pivotBound T hf t hT hlevels hcoh hc hsmall hfmod
    F E g hg Dq S reg hregular active sreg other greg ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD
    hφ hlip hout diagonal V hV Q q hQ hq hqQ hqeq hlog u v r s J hJ huv hshort hvJ hr hrs hrshort hqlog A hA0 hA hbudget
  have hcrt (y : ℝ) : correctedMixedPairAverage P Q q c y =
      ((∏ i, if active i then (1 : ℝ) else 1 - (reg i : ℝ)⁻¹ : ℝ) : ℂ) *
        correctedMixedPairAverage P Q R c0 y := by
    have hqR : q = (∏ i, reg i) * R := hqeq
    have hpR : pageAtModulus ((∏ i, reg i) * R) (selectedPageZero P Q) =
        pageAtModulus R (selectedPageZero P Q) := by simpa only [hqR] using hpage
    have hh := movingReducedPair_regular_page_average P Q p tier value hprime hdisjoint outside
      childBound pivotBound F E g Dq S T hf hlevels hsmall houtside reg hreg hregular hqs R rfl
      hpR active sreg other hsreg hother greg hgreg henergy y
    simpa only [← hqR] using hh
  change ‖_ - (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
    movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y) *
      (Real.exp (x - J) : ℂ) * correctedMixedPairAverage P Q q c y / (y : ℂ))‖ ≤ _ at hbase
  simp_rw [hcrt] at hbase
  exact hbase

end Ostmann

end OAI
