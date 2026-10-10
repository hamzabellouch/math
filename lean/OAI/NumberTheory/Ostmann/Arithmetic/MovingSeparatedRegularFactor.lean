import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedSupportedPair

namespace OAI

/-! # The original regular multiplier at the separated arithmetic modulus -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap

theorem movingOriginalSupportedSeparatedRegular_modulus_factor {σ I J : Type*} [Fintype J] (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (hcover : ∀ p ∈ outside, ∃ i ∈ S, q i = p)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (Jleft Jright : ℝ) (diagonal : Bool)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (t : Bool → FrequencyTree ℤ n)
    (hT : ∀ side, (T side).Follows (t side)) (hf : ∀ side, (T side).Frequencies (· ≠ 0))
    (hlevels : ∀ side, (T side).Levels tier) (hcoh : ∀ side, (T side).RegularCoherent)
    (hc : ∀ side, (T side).CompensationPrimeData value)
    (hsmall : ∀ side i, (T side).Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ side i, (T side).Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (R : ℤ) (hR : ∀ side, (T side).frequencyProduct ∣ R)
    (hsmallR : ∀ i, IsCoprime (value i : ℤ) R)
    (hden : ∀ side i, i ∈ S → (T side).ModularDenominators value (q i))
    (reg : J → ℕ) [∀ i, Fact (reg i).Prime]
    (hregular : ∀ side, MovingSlotReversal.naturalProduct value (T side).regularSlots = ∏ i, reg i)
    (active : J → Bool) (s : ℤ) (other : ∀ i, ZMod (reg i)) (greg : ∀ i, ZMod (reg i) → ℂ)
    (M : ℕ) (hfrequency : R ^ (n + 1) ∣ (M : ℤ))
    (hsquare : ∀ side, ∀ o ∈ (T side).occurrences,
      ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hspectator : ∀ i ∈ S, (q i : ℤ) ∣ M)
    (hregM : ∀ i, reg i ∣ M) (XL XR : ℕ) :
    let nodes := fun side => (T side).formulaNodes value (fun i => (hprime i).ne_zero)
      childBound pivotBound (hf side) (.prime false) (.prime true)
    let c := fun a b => movingSeparatedPairResidueCoefficient q value outside F E g Dq S T nodes R a b *
      (guardedRegularMultiplier reg active s other greg a b : ℂ)
    movingOriginalSupportedOuterPair q value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
        Jleft Jright diagonal T t XL XR *
        (naturalRegularMultiplier reg active s other greg XL XR : ℂ) =
      if XL.Coprime XR then c (XL % M) (XR % M) *
        movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal XL XR else 0 := by
  dsimp only
  let hv := fun i => (hprime i).ne_zero
  let nodes := fun side => (T side).formulaNodes value hv childBound pivotBound (hf side)
    (.prime false) (.prime true)
  let oldM := movingReducedPairModulus value hv outside childBound pivotBound T hf q S
  have he := movingOriginalSupportedOuterPair_reduced_factor q tier value hprime hdisjoint outside
    childBound pivotBound F E g hg Dq S ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD
    hφ hlip hout diagonal T t hT hf hlevels hcoh hc hsmall hfmod (∏ i, reg i) hregular XL XR
  have hback := movingReducedPairResidueCoefficient_modEq q value hv outside childBound pivotBound
    F E g Dq S T hf (XL % oldM) (XR % oldM) XL XR
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq XL oldM))
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq XR oldM))
  have hsep := movingReducedPairResidueCoefficient_eq_separated q tier value hprime hdisjoint outside
    childBound pivotBound F E g Dq S hcover (fun i _ => hg i) T hlevels hf hsmall hfmod R hR hsmallR
    (fun side => (hc side).distinct) hden XL XR
  have hforward := movingSeparatedPairResidueCoefficient_modEq q value outside F E g Dq S T nodes R hf hR
    XL XR (XL % M) (XR % M) M hfrequency hsquare hspectator
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq XL M).symm)
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq XR M).symm)
  dsimp only at he hsep
  rw [hback, hsep, hforward] at he
  have hm := multiply_regular_after_support reg active s other greg XL XR _ _ _ he
  have hgmod := guardedRegularMultiplier_modEq reg active s other greg XL XR (XL % M) (XR % M) M
    hregM (Nat.mod_modEq XL M).symm (Nat.mod_modEq XR M).symm
  rw [hgmod] at hm
  exact hm

end Ostmann

end OAI
