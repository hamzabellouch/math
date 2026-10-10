import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedPair

namespace OAI

/-! # The original supported prime pair at the separated arithmetic modulus -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap

/-- The literal product in the original sampled coefficient square. -/
noncomputable def movingOriginalSupportedPair {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (t : Bool → FrequencyTree ℤ n)
    (XL XR : ℕ) : ℂ :=
  movingSupportedWeight value outside (T false) XL XR
      (movingOriginalGiantWeight q value childBound pivotBound (F false) (E false) g (Dq false) S
        ψ X lo hi φ G (T false) (t false) XL XR) *
    conj (movingSupportedWeight value outside (T true) XL XR
      (movingOriginalGiantWeight q value childBound pivotBound (F true) (E true) g (Dq true) S
        ψ X lo hi φ G (T true) (t true) XL XR))

theorem movingOriginalSupportedPair_separated_factor {σ I : Type*} (q : I → ℕ)
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
    {n : ℕ} (T : Bool → MovingSlotData σ n) (t : Bool → FrequencyTree ℤ n)
    (hT : ∀ side, (T side).Follows (t side)) (hf : ∀ side, (T side).Frequencies (· ≠ 0))
    (hlevels : ∀ side, (T side).Levels tier) (hcoh : ∀ side, (T side).RegularCoherent)
    (hc : ∀ side, (T side).CompensationPrimeData value)
    (hsmall : ∀ side i, (T side).Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ side i, (T side).Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (R : ℤ) (hR : ∀ side, (T side).frequencyProduct ∣ R)
    (hsmallR : ∀ i, IsCoprime (value i : ℤ) R)
    (hden : ∀ side i, i ∈ S → (T side).ModularDenominators value (q i))
    (Reg : ℕ)
    (hregular : ∀ side, MovingSlotReversal.naturalProduct value (T side).regularSlots = Reg)
    (M : ℕ) (hfrequency : R ^ (n + 1) ∣ (M : ℤ))
    (hsquare : ∀ side, ∀ o ∈ (T side).occurrences,
      ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hspectator : ∀ i ∈ S, (q i : ℤ) ∣ M)
    (XL XR : ℕ) (hXL : XL.Coprime Reg) (hXR : XR.Coprime Reg) :
    let hv := fun i => (hprime i).ne_zero
    let nodes := fun side => (T side).formulaNodes value hv childBound pivotBound (hf side)
      (.prime false) (.prime true)
    let c := movingSeparatedPairResidueCoefficient q value outside F E g Dq S T nodes R
    movingOriginalSupportedPair q value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
        T t XL XR =
      if XL.Coprime XR then c (XL % M) (XR % M) *
        movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G XL XR else 0 := by
  let hv := fun i => (hprime i).ne_zero
  let nodes := fun side => (T side).formulaNodes value hv childBound pivotBound (hf side)
    (.prime false) (.prime true)
  let oldM := movingReducedPairModulus value hv outside childBound pivotBound T hf q S
  have ht := movingReducedPairModulus_tests value hv outside childBound pivotBound T hf q S
  have he := movingOriginalGiantWeight_reduced_pair_factor q tier value hprime hdisjoint outside
    childBound pivotBound F E g hg Dq S ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
    T t hT hf hlevels hcoh hc hsmall hfmod Reg hregular
    XL XR (XL % oldM) (XR % oldM) oldM ht.1 ht.2.1 ht.2.2.1 ht.2.2.2
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq XL oldM).symm)
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq XR oldM).symm)
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
  change movingOriginalSupportedPair q value outside childBound pivotBound F E g Dq S
    ψ X lo hi φ G T t XL XR =
    if XL.Coprime XR ∧ XL.Coprime Reg ∧ XR.Coprime Reg then
      movingReducedPairResidueCoefficient q value outside F E g Dq S T nodes
        (XL % oldM) (XR % oldM) *
        movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G XL XR else 0 at he
  dsimp only at hsep ⊢
  rw [hback, hsep, hforward] at he
  by_cases hp : XL.Coprime XR
  · rw [ite_eq_left ⟨hp, hXL, hXR⟩] at he
    rw [ite_eq_left hp]
    exact he
  · rw [ite_eq_right (fun h => hp h.1)] at he
    rw [ite_eq_right hp]
    exact he

end Ostmann

end OAI
