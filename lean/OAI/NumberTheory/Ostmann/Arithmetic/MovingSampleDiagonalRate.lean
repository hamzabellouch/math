import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedDiagonalRate
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleModulusRange
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullPageDeletion

namespace OAI

/-! # The mixed giant comparison for actual sampled histories -/

namespace Ostmann
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_original_sampled_diagonal_prime_rate (P : PublishedProgressionInput)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (Afreq Wwin B D : ℝ)
    (hAfreq : 0 ≤ Afreq) (hWwin : 0 ≤ Wwin) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (σ J : Type) [Fintype J] (p : Fin m → ℕ) [∀ i, Fact (p i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
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
      (Dq : Bool → ∀ i, (ZMod (p i))ˣ)
      (reg : J → ℕ) [∀ i, Fact (reg i).Prime]
      (_hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = ∏ i, reg i)
      (active : J → Bool) (sreg : ℤ) (other : ∀ i, ZMod (reg i)) (greg : ∀ i, ZMod (reg i) → ℂ)
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright : ℝ)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V Pmax cutoff : ℕ)
      (small bulk : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n),
      (∀ b, T b = buildMovingSlotData n (t b) (small b) (bulk b) (samples b)) →
      (∀ b, MovingLeafLengthLE n (small b) r₀) → (∀ b, MovingLeafLengthLE n (bulk b) m) →
      (∀ b, (T b).Frequencies (fun s => s.natAbs ≤ V)) →
      1 ≤ V → 1 ≤ Pmax → (∀ i, value i ≤ Pmax) →
      (Pmax : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L)) →
      (V : ℝ) ≤ Real.exp (Afreq * m) → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      outside.length ≤ m → (∀ q ∈ outside, q.Prime) →
      (∀ q ∈ outside, ∃ i, p i = q) → V < cutoff → (∀ i, cutoff ≤ value i) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, value i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      ∀ q : ℕ, ∀ hq : 1 ≤ q,
      ∀ hqeq : q = (∏ i, reg i) * movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf p Finset.univ,
      (∀ b, movingRegularOutsidePairwise value outside (T b)) →
      Pairwise (fun i j => (reg i).Coprime (reg j)) →
      (∀ i, (∏ j, reg j).Coprime (p i)) →
      (∀ i, (sreg : ZMod (reg i)) ≠ 0) → (∀ i, other i ≠ 0) →
      (∀ i, greg i 0 = 0) → (∀ i, (∑ x : ZMod (reg i), ‖greg i x‖ ^ 2) = reg i) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      (∀ b, ‖movingDataWeight (F b) (E b) (T b)‖ ≤ 1) →
      (∀ i z, ‖g i z‖ ≤ p i) →
      let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
      let c0 := movingReducedPairResidueCoefficient p value outside F E g Dq Finset.univ T nodes
      letI : NeZero q := ⟨by omega⟩
      letI : NeZero (movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf p Finset.univ) := ⟨by
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
              correctedMixedPairAverage P (giantProgressionCutoff L) (movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf p Finset.univ) c0 y) / (y : ℂ))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_original_reduced_diagonal_prime_rate ψ n r₀ k Afreq Wwin B D
    hAfreq hWwin hB hD, movingSample_pair_modulus_giant_range n r₀ k Afreq hAfreq]
    with L hrate hmod
  dsimp only
  intro σ J _ p _ tier value hprime hdisjoint outside childBound pivotBound T hf t hT
    hlevels hcoh hc hsmall hfmod F E g hg Dq reg _ hregular active sreg other greg
    X lo hi hlo hhi φ G Jleft Jright hφ hlip hout diagonal V Pmax cutoff small bulk samples
    hbuild hsmallLen hbulkLen hV hVpos hPpos hvalueP hPexp hVA hwindow hpupper
    houtLen houtPrime houtCover hVcut hlarge hdeleteValue hdeleteSpect
    q hq hqeq houtside hreg hqs hsreg hother hgreg henergy
    u v r s H hH huv hshort hvH hr hrs hrshort hweight hgnorm
  have hout0 : outside.prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hz
    exact (houtPrime 0 hz).ne_zero rfl
  have hout1 : 1 ≤ outside.prod := Nat.one_le_iff_ne_zero.mpr hout0
  have hbuild' : T = fun b => buildMovingSlotData n (t b) (small b) (bulk b) (samples b) :=
    funext hbuild
  have hfull : movingFullPairModulus value (fun i => (hprime i).ne_zero) outside
      childBound pivotBound T hf p Finset.univ ≤ giantProgressionCutoff L := by
    subst T
    exact hmod σ value (fun i => (hprime i).ne_zero) outside Pmax V hout1 houtLen
      (fun a ha => by obtain ⟨i, rfl⟩ := houtCover a ha; exact hpupper i)
      hPpos hVpos hvalueP hPexp hVA childBound pivotBound t small bulk samples hf
      hsmallLen hbulkLen hV p hpupper
  have hcop := movingOriginalRegular_coprime_reduced tier value hprime hdisjoint outside
    childBound pivotBound T hf hlevels hsmall houtside (∏ i, reg i) hregular p Finset.univ
    (fun i _ => hqs i)
  have hqQ : q ≤ giantProgressionCutoff L := by
    rw [hqeq]
    exact (Nat.le_of_dvd (movingFullPairModulus_pos value (fun i => (hprime i).ne_zero)
      outside hout0 childBound pivotBound T hf p Finset.univ
      (fun i _ => (Fact.out : (p i).Prime).pos))
      (movingSplitModulus_dvd_full value (fun i => (hprime i).ne_zero) outside
        childBound pivotBound T hf p Finset.univ (∏ i, reg i) (hregular false) hcop)).trans hfull
  have hpage : pageAtModulus q (selectedPageZero P (giantProgressionCutoff L)) =
      pageAtModulus (movingReducedPairModulus value (fun i => (hprime i).ne_zero)
        outside childBound pivotBound T hf p Finset.univ) (selectedPageZero P (giantProgressionCutoff L)) := by
    rw [hqeq]
    have hc' : (MovingSlotReversal.naturalProduct value (T false).regularSlots).Coprime
        (movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf p Finset.univ) := by
      simpa only [hregular false] using hcop
    have hh := movingSplitModulus_page_projection value hprime outside childBound pivotBound T hf
      p Finset.univ (fun i _ => (Fact.out : (p i).Prime)) houtPrime V cutoff hVcut hV
      (selectedPageZero P (giantProgressionCutoff L)) hdeleteValue
      (fun z hz q hq i _ => hdeleteSpect z hz q hq i)
      (by
        intro z hz q hq hmem
        obtain ⟨i, hi⟩ := houtCover q hmem
        exact hdeleteSpect z hz q hq i hi) hlarge hc'
    simpa only [hregular false] using hh
  have hVreal : ∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ (V : ℝ)) := by
    intro b
    exact (hV b).mono (fun s hs => by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using (Nat.cast_le (α := ℝ).mpr hs))
  exact hrate σ J p tier value hprime hdisjoint outside childBound pivotBound T hf t hT
    hlevels hcoh hc hsmall hfmod F E g hg Dq reg hregular active sreg other greg
    X lo hi hlo hhi φ G Jleft Jright hφ hlip hout diagonal V hVreal
    (Nat.cast_nonneg _) hVA hwindow hpupper q hq hqQ hqeq houtside hreg hqs hpage
    hsreg hother hgreg henergy u v r s H hH huv hshort hvH hr hrs hrshort hweight hgnorm

end Ostmann

end OAI
