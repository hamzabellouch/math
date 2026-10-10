import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportedPair
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullModulus
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterKernel

namespace OAI

/-! # Literal supported two-history weights with their original outer priors -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap

noncomputable def movingFullPairResidueCoefficient {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (a b : ℕ) : ℂ :=
  movingResidueSupportedWeight value outside (T false) a b
      (movingResidueCoefficient q value (F false) (E false) g (Dq false) S (T false) (nodes false) a b) *
    conj (movingResidueSupportedWeight value outside (T true) a b
      (movingResidueCoefficient q value (F true) (E true) g (Dq true) S (T true) (nodes true) a b))

noncomputable def movingOriginalSupportedOuterPair {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (t : Bool → FrequencyTree ℤ n) (XL XR : ℕ) : ℂ :=
  (movingSupportedWeight value outside (T false) XL XR
      (movingOriginalGiantWeight q value childBound pivotBound (F false) (E false) g (Dq false) S
        ψ X lo hi φ G (T false) (t false) XL XR) *
    conj (movingSupportedWeight value outside (T true) XL XR
      (movingOriginalGiantWeight q value childBound pivotBound (F true) (E true) g (Dq true) S
        ψ X lo hi φ G (T true) (t true) XL XR))) *
      giantOuterWeight φ Jleft Jright diagonal XL XR

theorem movingOriginalSupportedOuterPair_factor {σ I : Type*} (q : I → ℕ)
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
    (XL XR : ℕ) :
    let hv := fun i => (hprime i).ne_zero
    let M := movingFullPairModulus value hv outside childBound pivotBound T hf q S
    let nodes := fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true)
    let c := movingFullPairResidueCoefficient q value outside F E g Dq S T nodes
    movingOriginalSupportedOuterPair q value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
        Jleft Jright diagonal T t XL XR =
      if XL.Coprime XR then c (XL % M) (XR % M) *
        movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal XL XR else 0 := by
  dsimp only
  let hv := fun i => (hprime i).ne_zero
  let M := movingFullPairModulus value hv outside childBound pivotBound T hf q S
  have ht := movingFullPairModulus_tests value hv outside childBound pivotBound T hf q S
  have h := movingOriginalGiantWeight_supported_pair_factor q tier value hprime hdisjoint outside childBound pivotBound
    F E g hg Dq S ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout T t hT hf hlevels hcoh hc hsmall hfmod
    XL XR (XL % M) (XR % M) M ht.1 ht.2.1 ht.2.2.1 ht.2.2.2
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq XL M).symm)
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq XR M).symm)
  dsimp only [movingOriginalSupportedOuterPair]
  rw [h]
  by_cases hp : XL.Coprime XR
  · rw [ite_eq_left hp, ite_eq_left hp]
    exact mul_assoc _ _ _
  · rw [ite_eq_right hp, ite_eq_right hp, zero_mul]

end Ostmann

end OAI
