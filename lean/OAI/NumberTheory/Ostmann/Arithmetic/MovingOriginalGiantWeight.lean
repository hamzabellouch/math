import OAI.NumberTheory.Ostmann.Arithmetic.MovingRealKernel

namespace OAI

/-! # A name for the literal original recursive giant coefficient -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap

noncomputable def movingOriginalGiantWeight {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (XL XR : ℕ) : ℂ :=
  recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
    (fun x s => (movingWindowLeaf value X lo hi (movingDataLeaf F) x s *
      movingFourierLeaf value ψ X x s) *
        ∏ i ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g i) (Dq i) x s)
    (movingSlotCutoff value childBound pivotBound
      (movingPhiExtra value childBound pivotBound (movingDataExtra E) φ G)) n ⟨n, T, XL, XR⟩ t

theorem movingOriginalGiantWeight_factor {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL XR a b M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    movingOriginalGiantWeight q value childBound pivotBound F E g Dq S ψ X lo hi φ G T t XL XR =
      movingResidueCoefficient q value F E g Dq S T nodes a b *
        movingRealKernel value T nodes ψ X lo hi hlo hhi φ G XL XR :=
  moving_recursive_real_kernel q value hvalue childBound pivotBound F E g hg Dq S
    ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout T t hT hf XL XR a b M hM hMq hL hR

end Ostmann

end OAI
