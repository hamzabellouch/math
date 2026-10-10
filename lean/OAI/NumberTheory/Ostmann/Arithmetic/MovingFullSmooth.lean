import OAI.NumberTheory.Ostmann.Arithmetic.MovingSmoothPolynomials
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullFourier

namespace OAI

/-! # The full original smooth factor in the moving arithmetic coefficient -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- Every original logarithmic node cutoff and normalized Fourier leaf is
represented by the one constructed polynomial family. Arithmetic restrictions
and compensation powers stay in the original scalar coefficient. -/
theorem moving_full_smooth_polynomial {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hfreq : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (L R : Polynomial ℝ) (z : ℝ)
    (hL : L.eval z = (XL : ℝ)) (hR : R.eval z = (XR : ℝ)) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => movingWindowLeaf value X lo hi F x s * movingFourierLeaf value ψ X x s)
        (movingSlotCutoff value childBound pivotBound
          (movingPhiExtra value childBound pivotBound extra φ G)) n ⟨n, T, XL, XR⟩ t =
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (movingWindowLeaf value X lo hi F) (movingSlotCutoff value childBound pivotBound extra)
        n ⟨n, T, XL, XR⟩ t *
          smoothPolynomialWeight (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi
            φ G B D hB hD hφ hlip) z := by
  rw [movingSlotWeight_node_cutoff value childBound pivotBound _ extra φ G T t hT XL XR,
    moving_windowed_fourier_polynomial value hvalue childBound pivotBound F extra ψ X lo hi
      hlo hhi T t hT hfreq XL XR L R z hL hR]
  by_cases hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
      (movingWindowLeaf value X lo hi F) (movingSlotCutoff value childBound pivotBound extra)
      n ⟨n, T, XL, XR⟩ t = 0
  · simp only [hw, zero_mul]
  · have hI := movingSlotWeight_nonzero_integral value childBound pivotBound
      (movingWindowLeaf value X lo hi F) extra T t hT XL XR hw
    rw [movingNaturalNodeCutoff_eq_real value hvalue φ G T hfreq XL XR hI,
      movingSmoothPolynomialFactors_value value T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout z,
      hL, hR]
    ring

/-- The complete moving coefficient splits into the original scalar support,
its actual smooth polynomial weight, and all of its spectator trees. No
nonzero-term hypothesis is needed. -/
theorem moving_full_smooth_spectator_decomposition {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (hextra : ∀ i x s v w, extra x s v w ≠ 0 →
      (historyPivot (movingSlotSystem value childBound pivotBound) x s v w : ZMod (q i)) ≠ 0)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hfreq : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (L R : Polynomial ℝ) (z : ℝ)
    (hL : L.eval z = (XL : ℝ)) (hR : R.eval z = (XR : ℝ)) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => (movingWindowLeaf value X lo hi F x s * movingFourierLeaf value ψ X x s) *
          ∏ i ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g i) (Dq i) x s)
        (movingSlotCutoff value childBound pivotBound
          (movingPhiExtra value childBound pivotBound extra φ G)) n ⟨n, T, XL, XR⟩ t =
      (recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (movingWindowLeaf value X lo hi F) (movingSlotCutoff value childBound pivotBound extra)
        n ⟨n, T, XL, XR⟩ t *
          smoothPolynomialWeight (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi
            φ G B D hB hD hφ hlip) z) *
        ∏ i ∈ S, movingSlotSpectator value (g i) (Dq i) T XL XR := by
  have hcut : ∀ i x s v w, movingPhiExtra value childBound pivotBound extra φ G x s v w ≠ 0 →
      (historyPivot (movingSlotSystem value childBound pivotBound) x s v w : ZMod (q i)) ≠ 0 := by
    intro i x s v w h
    apply hextra i x s v w
    intro he
    exact h (by simp only [movingPhiExtra, he, zero_mul])
  rw [movingSlotWeight_spectator_product q value childBound pivotBound _ _ hcut g Dq S T t hT XL XR,
    moving_full_smooth_polynomial value hvalue childBound pivotBound F extra ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip hout T t hT hfreq XL XR L R z hL hR]

end Ostmann

end OAI
