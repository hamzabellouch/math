import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportedOuterFactor
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularResidues

namespace OAI

/-! # The original supported pair with the displayed regular-prime multiplier -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem movingOriginalSupportedRegular_factor {σ I J : Type*} [Fintype J] (q : I → ℕ)
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
    (reg : J → ℕ) [∀ i, Fact (reg i).Prime] (label : J → σ)
    (hlabel : ∀ i, value (label i) = reg i) (hmem : ∀ i, label i ∈ (T false).regularSlots)
    (active : J → Bool) (s : ℤ) (other : ∀ i, ZMod (reg i)) (greg : ∀ i, ZMod (reg i) → ℂ)
    (XL XR : ℕ) :
    let hv := fun i => (hprime i).ne_zero
    let M := movingFullPairModulus value hv outside childBound pivotBound T hf q S
    let nodes := fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true)
    let c := fun a b => movingFullPairResidueCoefficient q value outside F E g Dq S T nodes a b *
      (guardedRegularMultiplier reg active s other greg a b : ℂ)
    movingOriginalSupportedOuterPair q value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
        Jleft Jright diagonal T t XL XR *
        (naturalRegularMultiplier reg active s other greg XL XR : ℂ) =
      if XL.Coprime XR then c (XL % M) (XR % M) *
        movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal XL XR else 0 := by
  dsimp only
  let hv := fun i => (hprime i).ne_zero
  let M := movingFullPairModulus value hv outside childBound pivotBound T hf q S
  have hr := movingSupportedWeight_regular_multiplier value outside (T false) reg label hlabel hmem
    active s other greg XL XR
    (movingOriginalGiantWeight q value childBound pivotBound (F false) (E false) g (Dq false) S
      ψ X lo hi φ G (T false) (t false) XL XR)
  have hrpair : movingOriginalSupportedOuterPair q value outside childBound pivotBound F E g Dq S
      ψ X lo hi φ G Jleft Jright diagonal T t XL XR *
        (naturalRegularMultiplier reg active s other greg XL XR : ℂ) =
      movingOriginalSupportedOuterPair q value outside childBound pivotBound F E g Dq S
      ψ X lo hi φ G Jleft Jright diagonal T t XL XR *
        (guardedRegularMultiplier reg active s other greg XL XR : ℂ) := by
    unfold movingOriginalSupportedOuterPair
    convert congrArg (fun z : ℂ => z *
      conj (movingSupportedWeight value outside (T true) XL XR
        (movingOriginalGiantWeight q value childBound pivotBound (F true) (E true) g (Dq true) S
          ψ X lo hi φ G (T true) (t true) XL XR)) * giantOuterWeight φ Jleft Jright diagonal XL XR) hr using 1 <;> ring
  have hk := movingOriginalSupportedOuterPair_factor q tier value hprime hdisjoint outside childBound pivotBound
    F E g hg Dq S ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal
    T t hT hf hlevels hcoh hc hsmall hfmod XL XR
  dsimp only at hk
  have hm := guardedRegularMultiplier_full_modulus value hv outside childBound pivotBound T hf q S
    reg label hlabel hmem active s other greg XL XR
  dsimp only at hm
  rw [hrpair, hk]
  by_cases hp : XL.Coprime XR
  · rw [ite_eq_left hp, ite_eq_left hp, hm]
    ring
  · rw [ite_eq_right hp, ite_eq_right hp, zero_mul]

end Ostmann

end OAI
