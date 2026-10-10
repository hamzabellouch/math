import OAI.NumberTheory.Ostmann.Arithmetic.MovingWindowCells
import OAI.NumberTheory.Ostmann.ZeroDensity.MovingFullSmoothZero
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSpectatorCells

namespace OAI

/-! # The complete nonsmooth factor of the original moving coefficient -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingWindowedSpectatorWeight {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (X lo hi : ℝ) (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) : ℂ :=
  movingUnrestrictedWeight value (movingWindowLeaf value X lo hi (movingDataLeaf F))
    (movingDataExtra E) T XL XR * ∏ i ∈ S, movingSlotSpectator value (g i) (D i) T XL XR

theorem movingWindowedSpectatorWeight_norm {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (X lo hi : ℝ) (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (B : I → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hg : ∀ i ∈ S, ∀ z, ‖g i z‖ ≤ B i)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) :
    ‖movingWindowedSpectatorWeight q value F E X lo hi g D S T XL XR‖ ≤
      ‖movingDataWeight F E T‖ * ∏ i ∈ S, B i ^ (2 ^ n) := by
  rw [movingWindowedSpectatorWeight, norm_mul]
  have hscalar : ‖movingUnrestrictedWeight value
      (movingWindowLeaf value X lo hi (movingDataLeaf F)) (movingDataExtra E) T XL XR‖ ≤
      ‖movingDataWeight F E T‖ := by
    rw [movingUnrestrictedWeight_data_window]
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (movingDataWeight F E T)
  exact mul_le_mul hscalar (movingSpectatorProduct_norm q value g D S B hB hg T XL XR)
    (norm_nonneg _) (norm_nonneg _)

theorem movingWindowedSpectatorWeight_cells {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (X lo hi : ℝ) (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR M XL YL : ℕ)
    (hM : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (roots : Finset ℝ)
    (hroots : movingWindowRootCuts value T Polynomial.X (Polynomial.C XR) X lo hi ⊆ roots)
    (hX : T.Integral value XL XR) (hY : T.Integral value YL XR)
    (hres : (XL : ℤ) ≡ (YL : ℤ) [ZMOD M])
    (hcode : rootCellCode roots (XL : ℝ) = rootCellCode roots (YL : ℝ)) :
    movingWindowedSpectatorWeight q value F E X lo hi g D S T XL XR =
      movingWindowedSpectatorWeight q value F E X lo hi g D S T YL XR := by
  unfold movingWindowedSpectatorWeight
  rw [movingUnrestrictedWeight_data_window, movingUnrestrictedWeight_data_window]
  have hwin := movingNaturalWindows_of_rootCell value hvalue T hf XR XL YL X lo hi roots hroots hcode hX hY
  simp only [hwin]
  rw [movingSpectatorProduct_modEq q value hvalue g D S T hf M XL XR YL hM hX hY hres]

/-- This identity includes all original arithmetic guards, terminal windows,
smooth factors, compensation weights, and spectators. -/
theorem moving_complete_coefficient_factor {σ I : Type*} (q : I → ℕ)
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
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => (movingWindowLeaf value X lo hi (movingDataLeaf F) x s *
          movingFourierLeaf value ψ X x s) *
            ∏ i ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g i) (Dq i) x s)
        (movingSlotCutoff value childBound pivotBound
          (movingPhiExtra value childBound pivotBound (movingDataExtra E) φ G)) n ⟨n, T, XL, XR⟩ t =
      (movingArithmeticIndicator value childBound pivotBound T XL XR *
        movingWindowedSpectatorWeight q value F E X lo hi g Dq S T XL XR) *
          smoothPolynomialWeight (movingSmoothPolynomialFactors value T Polynomial.X (Polynomial.C XR)
            ψ X lo hi hlo hhi φ G B D hB hD hφ hlip) XL := by
  rw [moving_full_smooth_spectator_of_zero q value hvalue childBound pivotBound
    (movingDataLeaf F) (movingDataExtra E) g hg Dq S ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
    T t hT hf XL XR Polynomial.X (Polynomial.C XR) XL (by simp) (by simp)]
  rw [movingSlotWeight_indicator_factor value hvalue childBound pivotBound
    (movingWindowLeaf value X lo hi (movingDataLeaf F)) (movingDataExtra E) T t hT hf XL XR]
  unfold movingWindowedSpectatorWeight
  ring

end Ostmann

end OAI
