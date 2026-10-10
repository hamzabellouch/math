import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedSupport

namespace OAI

/-! # Exact original-weight factorization with the regular units extracted -/

namespace Ostmann
open scoped Classical SchwartzMap

theorem movingOriginalGiantWeight_reduced_factor {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hlevels : T.Levels tier) (hcoh : T.RegularCoherent) (hc : T.CompensationPrimeData value)
    (hf : T.Frequencies (· ≠ 0))
    (hsmall : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (XL XR a b M : ℕ)
    (hM : movingTopPeriod value (fun i => (hprime i).ne_zero) childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hunit : movingAuxiliaryUnitPeriod value outside T ∣ (M : ℤ))
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound hf (.prime false) (.prime true)
    movingSupportedWeight value outside T XL XR
      (movingOriginalGiantWeight q value childBound pivotBound F E g Dq S ψ X lo hi φ G T t XL XR) =
      if XL.Coprime XR ∧
          XL.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) ∧
          XR.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) then
        movingReducedResidueWeight value outside T a b
          (movingResidueCoefficient q value F E g Dq S T nodes a b) *
            movingRealKernel value T nodes ψ X lo hi hlo hhi φ G XL XR else 0 := by
  dsimp only
  have hvalue : ∀ i, value i ≠ 0 := fun i => (hprime i).ne_zero
  rw [movingSupportedWeight_reduced_residue tier value hprime hdisjoint outside T hlevels hcoh hc hf
    hsmall hfmod XL XR a b M _
    (movingOriginalGiantWeight_integral q value hvalue childBound pivotBound F E g Dq S
      ψ X lo hi φ G T t hT hf XL XR) hunit hsquare hL hR,
    movingOriginalGiantWeight_factor q value hvalue childBound pivotBound F E g hg Dq S
      ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout T t hT hf XL XR a b M hM hMq hL hR]
  split_ifs
  · unfold movingReducedResidueWeight
    split_ifs <;> simp
  · rfl

end Ostmann

end OAI
