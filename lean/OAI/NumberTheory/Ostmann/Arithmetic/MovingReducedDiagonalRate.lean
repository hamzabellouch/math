import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedDiagonalComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterVariationScale
import OAI.NumberTheory.Ostmann.Construction.RegularMultiplierNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantBounds

namespace OAI

/-! # Numerical giant comparison for the original diagonal -/

namespace Ostmann
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_original_reduced_diagonal_prime_rate (P : PublishedProgressionInput)
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
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      0 ≤ V → V ≤ Real.exp (Afreq * m) → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, q ≤ giantProgressionCutoff L →
      ∀ hqeq : q = (∏ i, reg i) * movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf p Finset.univ,
      (∀ b, movingRegularOutsidePairwise value outside (T b)) →
      Pairwise (fun i j => (reg i).Coprime (reg j)) →
      (∀ i, (∏ j, reg j).Coprime (p i)) →
      pageAtModulus q (selectedPageZero P (giantProgressionCutoff L)) =
        pageAtModulus (movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside childBound pivotBound T hf p Finset.univ) (selectedPageZero P (giantProgressionCutoff L)) →
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
  obtain ⟨C, hC, hbudget⟩ := moving_outer_variation_scale ψ n r₀ k Afreq Wwin B D 1
    hAfreq hWwin (by norm_num)
  filter_upwards [P.moving_original_reduced_diagonal_haar_rate n C 2,
    eventually_ge_atTop (200 : ℝ)] with L hrate hL
  dsimp only
  intro σ J _ p _ tier value hprime hdisjoint outside childBound pivotBound T hf t hT
    hlevels hcoh hc hsmall hfmod F E g hg Dq reg _ hregular active sreg other greg
    X lo hi hlo hhi φ G Jleft Jright hφ hlip hout diagonal V hV hV0 hVA hwindow hpupper
    q hq hqQ hqeq houtside hreg hqs hpage hsreg hother hgreg henergy
    u v r s H hH huv hshort hvH hr hrs hrshort hweight hgnorm
  let R := movingReducedPairModulus value (fun i => (hprime i).ne_zero)
    outside childBound pivotBound T hf p Finset.univ
  have hR : 0 < R := by
    apply Nat.pos_of_ne_zero
    intro hz
    change q = (∏ i, reg i) * R at hqeq
    rw [hz, mul_zero] at hqeq
    omega
  have hregq : (∏ i, reg i) ≤ q := by
    change q = (∏ i, reg i) * R at hqeq
    rw [hqeq]
    exact Nat.le_mul_of_pos_right _ hR
  have hqlog := giantProgressionCutoff_log_le (by omega : 0 < q) hqQ
  have hregbound : (∏ i, (reg i : ℝ)) ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) := by
    rw [← Nat.cast_prod]
    apply (Nat.cast_le.mpr hregq).trans
    exact (Real.log_le_iff_le_exp (by exact_mod_cast (show 0 < q by omega))).mp hqlog
  let amp := (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 * ∏ j, (reg j : ℝ)
  have hamp0 : 0 ≤ amp := by dsimp only [amp]; positivity
  have hamp : amp ≤ 4 * (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 *
      Real.exp (1 * L + 1 * L * Real.exp ((12 / 1000 : ℝ) * L)) := by
    have hL1 : 1 ≤ L := by linarith only [hL]
    have hcoef : Real.exp ((12 / 1000 : ℝ) * L) ≤
        1 * L + 1 * L * Real.exp ((12 / 1000 : ℝ) * L) := by
      have hh := le_mul_of_one_le_left (Real.exp_nonneg ((12 / 1000 : ℝ) * L)) hL1
      linarith only [hh, hL1]
    have hh := hregbound.trans (Real.exp_le_exp.mpr hcoef)
    apply (mul_le_mul_of_nonneg_left hh (sq_nonneg _)).trans
    nlinarith only [mul_nonneg (sq_nonneg (∏ i, (p i : ℝ) ^ (2 ^ n)))
      (Real.exp_nonneg (1 * L + 1 * L * Real.exp ((12 / 1000 : ℝ) * L)))]
  have hb := hbudget L (by linarith only [hL]) p V lo hi amp diagonal
    hV0 hVA hhi hwindow hpupper hamp0 hamp
  have hQ := giantProgressionCutoff_bounds L hL
  apply hrate σ (Fin (spectatorBulkCount k L)) J p tier value hprime hdisjoint outside
    childBound pivotBound T hf t hT hlevels hcoh hc hsmall hfmod F E g hg Dq Finset.univ
    reg hregular active sreg other greg ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD
    hφ hlip hout diagonal V hV (giantProgressionCutoff L) q hQ.1 hq hqQ hqeq houtside
    hreg (fun i _ => hqs i) hpage hsreg hother hgreg henergy hQ.2
    u v r s H hH huv hshort hvH hr hrs hrshort hqlog amp hamp0 _ hb
  intro a ha b hb
  exact movingReducedPair_with_regular_norm p reg value outside F E g hgnorm Dq T _
    hweight active sreg other greg henergy a b

end Ostmann

end OAI
