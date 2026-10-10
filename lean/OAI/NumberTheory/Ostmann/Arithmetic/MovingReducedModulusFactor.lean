import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedCRT

namespace OAI

/-! # The extracted original coefficient at any common regular/auxiliary modulus -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem movingOriginalSupportedReducedRegular_modulus_factor {σ I J : Type*} [Fintype J] (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (t : Bool → FrequencyTree ℤ n)
    (hT : ∀ b, (T b).Follows (t b)) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hlevels : ∀ b, (T b).Levels tier) (hcoh : ∀ b, (T b).RegularCoherent)
    (hc : ∀ b, (T b).CompensationPrimeData value)
    (hsmall : ∀ b i, (T b).Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ b i, (T b).Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (reg : J → ℕ) [∀ i, Fact (reg i).Prime]
    (hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = ∏ i, reg i)
    (active : J → Bool) (s : ℤ) (other : ∀ i, ZMod (reg i)) (greg : ∀ i, ZMod (reg i) → ℂ)
    (M : ℕ)
    (hM : movingReducedPairModulus value (fun i => (hprime i).ne_zero) outside
      childBound pivotBound T hf q S ∣ M)
    (hregM : ∀ i, reg i ∣ M) (XL XR : ℕ) :
    let hv := fun i => (hprime i).ne_zero
    let nodes := fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true)
    let c := fun a b => movingReducedPairResidueCoefficient q value outside F E g Dq S T nodes a b *
      (guardedRegularMultiplier reg active s other greg a b : ℂ)
    movingOriginalSupportedOuterPair q value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
        Jleft Jright diagonal T t XL XR *
        (naturalRegularMultiplier reg active s other greg XL XR : ℂ) =
      if XL.Coprime XR then
        c (XL % M) (XR % M) *
        movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal XL XR else 0 := by
  dsimp only
  let hv := fun i => (hprime i).ne_zero
  let R := movingReducedPairModulus value hv outside childBound pivotBound T hf q S
  let nodes := fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true)
  let C := movingReducedPairResidueCoefficient q value outside F E g Dq S T nodes
  have he := movingOriginalSupportedReducedRegular_factor q tier value hprime hdisjoint outside
    childBound pivotBound F E g hg Dq S ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD
    hφ hlip hout diagonal T t hT hf hlevels hcoh hc hsmall hfmod reg hregular active s other greg XL XR
  dsimp only at he
  have hcoef : C (XL % R) (XR % R) = C (XL % M) (XR % M) := by
    apply movingReducedPairResidueCoefficient_modEq q value hv outside childBound pivotBound F E g Dq S T hf
    · exact Int.natCast_modEq_iff.mpr ((Nat.mod_modEq XL R).trans
        (((Nat.mod_modEq XL M).of_dvd hM).symm))
    · exact Int.natCast_modEq_iff.mpr ((Nat.mod_modEq XR R).trans
        (((Nat.mod_modEq XR M).of_dvd hM).symm))
  have hgmod := guardedRegularMultiplier_modEq reg active s other greg XL XR (XL % M) (XR % M) M
    hregM (Nat.mod_modEq XL M).symm (Nat.mod_modEq XR M).symm
  change _ = if XL.Coprime XR then (C (XL % M) (XR % M) *
    (guardedRegularMultiplier reg active s other greg (XL % M) (XR % M) : ℂ)) * _ else 0
  change _ = if XL.Coprime XR then (C (XL % R) (XR % R) *
    (guardedRegularMultiplier reg active s other greg XL XR : ℂ)) * _ else 0 at he
  rw [hcoef, hgmod] at he
  exact he

end Ostmann

end OAI
