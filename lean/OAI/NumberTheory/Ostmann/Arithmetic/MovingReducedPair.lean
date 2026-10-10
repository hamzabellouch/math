import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.MovingKernelPair

namespace OAI

/-! # The two original histories with a common regular-prime block extracted -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem movingOriginalGiantWeight_reduced_pair_factor {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (t : Bool → FrequencyTree ℤ n)
    (hT : ∀ b, (T b).Follows (t b)) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hlevels : ∀ b, (T b).Levels tier) (hcoh : ∀ b, (T b).RegularCoherent)
    (hc : ∀ b, (T b).CompensationPrimeData value)
    (hsmall : ∀ b i, (T b).Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ b i, (T b).Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (R : ℕ) (hregular : ∀ b, MovingSlotReversal.naturalProduct value (T b).regularSlots = R)
    (XL XR a b M : ℕ)
    (hM : ∀ b, movingTopPeriod value (fun i => (hprime i).ne_zero) childBound pivotBound (T b) (hf b) ∣ M)
    (hMq : ∀ b, ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value (T b) ∣ (M : ℤ))
    (hunit : ∀ b, movingAuxiliaryUnitPeriod value outside (T b) ∣ (M : ℤ))
    (hsquare : ∀ b, ∀ o ∈ (T b).occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := fun b => (T b).formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound (hf b) (.prime false) (.prime true)
    let c := fun side => movingReducedResidueWeight value outside (T side) a b
      (movingResidueCoefficient q value (F side) (E side) g (Dq side) S (T side) (nodes side) a b)
    movingSupportedWeight value outside (T false) XL XR
      (movingOriginalGiantWeight q value childBound pivotBound (F false) (E false) g (Dq false) S
        ψ X lo hi φ G (T false) (t false) XL XR) *
      conj (movingSupportedWeight value outside (T true) XL XR
        (movingOriginalGiantWeight q value childBound pivotBound (F true) (E true) g (Dq true) S
          ψ X lo hi φ G (T true) (t true) XL XR)) =
      if XL.Coprime XR ∧ XL.Coprime R ∧ XR.Coprime R then (c false * conj (c true)) *
        movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G XL XR else 0 := by
  dsimp only
  rw [movingOriginalGiantWeight_reduced_factor q tier value hprime hdisjoint outside childBound pivotBound
    (F false) (E false) g hg (Dq false) S ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
    (T false) (t false) (hT false) (hlevels false) (hcoh false) (hc false) (hf false)
    (hsmall false) (hfmod false) XL XR a b M (hM false) (hMq false) (hunit false) (hsquare false) hL hR,
    movingOriginalGiantWeight_reduced_factor q tier value hprime hdisjoint outside childBound pivotBound
    (F true) (E true) g hg (Dq true) S ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
    (T true) (t true) (hT true) (hlevels true) (hcoh true) (hc true) (hf true)
    (hsmall true) (hfmod true) XL XR a b M (hM true) (hMq true) (hunit true) (hsquare true) hL hR]
  simp only [hregular]
  by_cases hp : XL.Coprime XR ∧ XL.Coprime R ∧ XR.Coprime R
  · rw [ite_eq_left hp, ite_eq_left hp, ite_eq_left hp, map_mul, movingRealKernelPair]
    ring
  · rw [ite_eq_right hp, ite_eq_right hp, ite_eq_right hp, map_zero, mul_zero]

end Ostmann

end OAI
