import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalGiantWeight
import OAI.NumberTheory.Ostmann.Arithmetic.MovingKernelPair

namespace OAI

/-! # The original product of histories has the paired real kernel -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem movingOriginalGiantWeight_paired_factor {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
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
    (XL XR a b M : ℕ)
    (hM : ∀ b, movingTopPeriod value hvalue childBound pivotBound (T b) (hf b) ∣ M)
    (hMq : ∀ b, ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value (T b) ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
    movingOriginalGiantWeight q value childBound pivotBound (F false) (E false) g (Dq false) S
        ψ X lo hi φ G (T false) (t false) XL XR *
      conj (movingOriginalGiantWeight q value childBound pivotBound (F true) (E true) g (Dq true) S
        ψ X lo hi φ G (T true) (t true) XL XR) =
      (movingResidueCoefficient q value (F false) (E false) g (Dq false) S (T false) (nodes false) a b *
        conj (movingResidueCoefficient q value (F true) (E true) g (Dq true) S (T true) (nodes true) a b)) *
      movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G XL XR := by
  dsimp only
  rw [movingOriginalGiantWeight_factor q value hvalue childBound pivotBound (F false) (E false) g hg
    (Dq false) S ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout (T false) (t false) (hT false)
    (hf false) XL XR a b M (hM false) (hMq false) hL hR,
    movingOriginalGiantWeight_factor q value hvalue childBound pivotBound (F true) (E true) g hg
    (Dq true) S ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout (T true) (t true) (hT true)
    (hf true) XL XR a b M (hM true) (hMq true) hL hR,
    map_mul, movingRealKernelPair]
  ring

end Ostmann

end OAI
