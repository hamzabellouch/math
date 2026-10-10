import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedPair
import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedModulus
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportedOuterFactor
import OAI.NumberTheory.Ostmann.Arithmetic.GuardedRegularCRT

namespace OAI

/-! # Original outer priors with the regular block removed from the residue coefficient -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap

noncomputable def movingReducedPairResidueCoefficient {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (a b : ℕ) : ℂ :=
  movingReducedResidueWeight value outside (T false) a b
      (movingResidueCoefficient q value (F false) (E false) g (Dq false) S (T false) (nodes false) a b) *
    conj (movingReducedResidueWeight value outside (T true) a b
      (movingResidueCoefficient q value (F true) (E true) g (Dq true) S (T true) (nodes true) a b))

theorem movingOriginalSupportedOuterPair_reduced_factor {σ I : Type*} (q : I → ℕ)
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
    (R : ℕ) (hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = R)
    (XL XR : ℕ) :
    let hv := fun i => (hprime i).ne_zero
    let M := movingReducedPairModulus value hv outside childBound pivotBound T hf q S
    let nodes := fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true)
    let c := movingReducedPairResidueCoefficient q value outside F E g Dq S T nodes
    movingOriginalSupportedOuterPair q value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
        Jleft Jright diagonal T t XL XR =
      if XL.Coprime XR ∧ XL.Coprime R ∧ XR.Coprime R then c (XL % M) (XR % M) *
        movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal XL XR else 0 := by
  dsimp only
  let hv := fun i => (hprime i).ne_zero
  let M := movingReducedPairModulus value hv outside childBound pivotBound T hf q S
  have ht := movingReducedPairModulus_tests value hv outside childBound pivotBound T hf q S
  have h := movingOriginalGiantWeight_reduced_pair_factor q tier value hprime hdisjoint outside childBound pivotBound
    F E g hg Dq S ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout T t hT hf hlevels hcoh hc hsmall hfmod
    R hregular XL XR (XL % M) (XR % M) M ht.1 ht.2.1 ht.2.2.1 ht.2.2.2
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq XL M).symm)
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq XR M).symm)
  dsimp only [movingOriginalSupportedOuterPair]
  rw [h]
  by_cases hp : XL.Coprime XR ∧ XL.Coprime R ∧ XR.Coprime R
  · rw [ite_eq_left hp, ite_eq_left hp]
    exact mul_assoc _ _ _
  · rw [ite_eq_right hp, ite_eq_right hp, zero_mul]

theorem movingOriginalSupportedReducedRegular_factor {σ I J : Type*} [Fintype J] (q : I → ℕ)
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
    (XL XR : ℕ) :
    let hv := fun i => (hprime i).ne_zero
    let M := movingReducedPairModulus value hv outside childBound pivotBound T hf q S
    let nodes := fun b => (T b).formulaNodes value hv childBound pivotBound (hf b) (.prime false) (.prime true)
    let c := movingReducedPairResidueCoefficient q value outside F E g Dq S T nodes
    movingOriginalSupportedOuterPair q value outside childBound pivotBound F E g Dq S ψ X lo hi φ G
        Jleft Jright diagonal T t XL XR *
        (naturalRegularMultiplier reg active s other greg XL XR : ℂ) =
      if XL.Coprime XR then
        (c (XL % M) (XR % M) * (guardedRegularMultiplier reg active s other greg XL XR : ℂ)) *
        movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal XL XR else 0 := by
  dsimp only
  apply multiply_regular_after_support reg active s other greg XL XR
  exact movingOriginalSupportedOuterPair_reduced_factor q tier value hprime hdisjoint outside childBound pivotBound
    F E g hg Dq S ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal
    T t hT hf hlevels hcoh hc hsmall hfmod (∏ i, reg i) hregular XL XR

end Ostmann

end OAI
