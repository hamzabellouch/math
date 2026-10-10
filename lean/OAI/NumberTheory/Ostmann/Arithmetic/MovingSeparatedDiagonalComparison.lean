import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedRegularFactor
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterCoprimeComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedPageAverage

namespace OAI

/-! # Original diagonal giant comparison after integrating the regular primes -/

namespace Ostmann
universe u v w
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_original_separated_diagonal_haar_rate (P : PublishedProgressionInput)
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
      (R : ℤ) (_hR : ∀ b, (T b).frequencyProduct ∣ R)
      (_hsmallR : ∀ i, IsCoprime (value i : ℤ) R)
      (_hden : ∀ b i, i ∈ S → (T b).ModularDenominators value (p i))
      (_hcover : ∀ q ∈ outside, ∃ i ∈ S, p i = q)
      (reg : J → ℕ) [∀ i, Fact (reg i).Prime]
      (_hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = ∏ i, reg i)
      (active : J → Bool) (sreg : ℤ) (other : ∀ i, ZMod (reg i)) (greg : ∀ i, ZMod (reg i) → ℂ)
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ M : ℕ, ∀ _hM : NeZero M,
      R ^ (n + 1) ∣ (M : ℤ) →
      (∀ b, ∀ o ∈ (T b).occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ (M : ℤ)) →
      (∀ i ∈ S, (p i : ℤ) ∣ (M : ℤ)) →
      (∏ i, reg i).Coprime M →
      ∀ Q q : ℕ, 2 ≤ Q → ∀ hq : 1 ≤ q, q ≤ Q →
      ∀ hqeq : q = (∏ i, reg i) * M,
      (∀ b, movingRegularOutsidePairwise value outside (T b)) →
      Pairwise (fun i j => (reg i).Coprime (reg j)) →
      (∀ i ∈ S, (∏ j, reg j).Coprime (p i)) →
      pageAtModulus q (selectedPageZero P Q) =
        pageAtModulus (M) (selectedPageZero P Q) →
      (∀ i, (sreg : ZMod (reg i)) ≠ 0) → (∀ i, other i ≠ 0) →
      (∀ i, greg i 0 = 0) → (∀ i, (∑ x : ZMod (reg i), ‖greg i x‖ ^ 2) = reg i) →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
      let c0 := movingSeparatedPairResidueCoefficient p value outside F E g Dq S T nodes R
      let c := fun a b => movingSeparatedPairResidueCoefficient p value outside F E g Dq S T nodes R a b *
        (guardedRegularMultiplier reg active sreg other greg a b : ℂ)
      ∀ A : ℝ, 0 ≤ A → (∀ a < q, ∀ b < q, ‖c a b‖ ≤ A) →
      2 * (A * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      let : NeZero q := ⟨by omega⟩
      let : NeZero (M) := ⟨by
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
              correctedMixedPairAverage P Q (M) c0 y) / (y : ℂ))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_outer_coprime_mixed_haar_rate n C d] with L hL
  intro σ I J _ p _ tier value hprime hdisjoint outside childBound pivotBound T hf t hT
    hlevels hcoh hc hsmall hfmod F E g hg Dq S R hR hsmallR hden hcover
    reg instReg hregular active sreg other greg ψ X lo hi hlo hhi φ G
    Jleft Jright B D hB hD hφ hlip hout diagonal V hV M hM hfrequency hsquare hspectator hcop
    Q q hQ hq hqQ hqeq houtside hreg hqs hpage hsreg hother hgreg henergy hlog
    u v r s J0 hJ huv hshort hvJ hr hrs hrshort hqlog
  dsimp only
  intro A hA0 hA hbudget
  let : NeZero M := hM
  let : NeZero q := ⟨by omega⟩
  let : ∀ i, NeZero (reg i) := fun i => ⟨(Fact.out : (reg i).Prime).ne_zero⟩
  let : NeZero (∏ i, reg i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (Fact.out : (reg i).Prime).ne_zero)⟩
  let : NeZero ((∏ i, reg i) * M) := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
  let c0 := movingSeparatedPairResidueCoefficient p value outside F E g Dq S T nodes R
  let c := fun a b => c0 a b * (guardedRegularMultiplier reg active sreg other greg a b : ℂ)
  have hbase := hL σ value (fun i => (hprime i).ne_zero) childBound pivotBound T hf ψ X lo hi hlo hhi
    φ G Jleft Jright B D hB hD hφ hlip hout diagonal V hV Q q hQ hq hqQ hlog
    u v r s J0 hJ huv hshort hvJ hr hrs hrshort hqlog c A hA0 hA hbudget
  dsimp only at hbase
  have hfactor (x y : ℕ) :
      movingOriginalSupportedOuterPair p value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
        Jleft Jright diagonal T t x y *
          (naturalRegularMultiplier reg active sreg other greg x y : ℂ) =
      if x.Coprime y then c (x % q) (y % q) *
        movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal x y else 0 := by
    have hMq : M ∣ q := by rw [hqeq]; exact dvd_mul_left _ _
    exact movingOriginalSupportedSeparatedRegular_modulus_factor p tier value hprime hdisjoint outside
      childBound pivotBound F E g hg Dq S hcover ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
      Jleft Jright diagonal T t hT hf hlevels hcoh hc hsmall hfmod R hR hsmallR hden
      reg hregular active sreg other greg q
      (hfrequency.trans (by exact_mod_cast hMq))
      (fun b o ho i hi => (hsquare b o ho i hi).trans (by exact_mod_cast hMq))
      (fun i hi => (hspectator i hi).trans (by exact_mod_cast hMq))
      (fun i => by rw [hqeq]; exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem reg (Finset.mem_univ i)) M) x y
  have hperiod (a b c d : ℕ) (hab : Nat.ModEq M a c) (hbd : Nat.ModEq M b d) : c0 a b = c0 c d := by
    exact movingSeparatedPairResidueCoefficient_modEq p value outside F E g Dq S T nodes R hf hR
      a b c d M hfrequency hsquare hspectator
      (Int.natCast_modEq_iff.mpr hab) (Int.natCast_modEq_iff.mpr hbd)
  have hcrt (y : ℝ) : correctedMixedPairAverage P Q q c y =
      ((∏ i, if active i then (1 : ℝ) else 1 - (reg i : ℝ)⁻¹ : ℝ) : ℂ) *
        correctedMixedPairAverage P Q M c0 y := by
    have hpM : pageAtModulus ((∏ i, reg i) * M) (selectedPageZero P Q) =
        pageAtModulus M (selectedPageZero P Q) := by simpa only [hqeq] using hpage
    have hh := periodic_coefficient_regular_page_average P Q reg hreg M hcop hpM
      active sreg other hsreg hother greg hgreg henergy c0 hperiod y
    simpa only [← hqeq] using hh
  simp_rw [hfactor]
  simpa only [hcrt] using hbase

end Ostmann

end OAI
