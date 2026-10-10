import OAI.NumberTheory.Ostmann.ZeroDensity.MovingSpectatorZero
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullSmooth

namespace OAI

/-! # Full smooth coefficients with only the actual spectator zero convention -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap

/-- Factor every spectator while retaining the full smooth and arithmetic
coefficient. This identity includes zero-support terms. -/
theorem movingSlotWeight_spectator_product_of_zero {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => F x s * ∏ i ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g i) (D i) x s)
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t =
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t *
        ∏ i ∈ S, movingSlotSpectator value (g i) (D i) T XL XR := by
  induction S using Finset.induction_on generalizing F with
  | empty => simp only [Finset.prod_empty, mul_one]
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    have he : (fun x s => F x s * (spectatorHistoryLeaf (movingSlotModulus value) (g i) (D i) x s *
        ∏ j ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g j) (D j) x s)) =
        (fun x s => (F x s * ∏ j ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g j) (D j) x s) *
          spectatorHistoryLeaf (movingSlotModulus value) (g i) (D i) x s) := by
      funext x s
      ring
    rw [he, movingSlotWeight_spectator_of_zero value childBound pivotBound _ extra
      (g i) (hg i) (D i) T t hT XL XR, ih]
    ring

/-- The complete moving coefficient splits into the original scalar support,
its actual smooth polynomial weight, and all of its spectator trees. No
nonzero-term hypothesis is needed. -/
theorem moving_full_smooth_spectator_of_zero {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
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
  rw [movingSlotWeight_spectator_product_of_zero q value childBound pivotBound _ _ g hg Dq S T t hT XL XR,
    moving_full_smooth_polynomial value hvalue childBound pivotBound F extra ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip hout T t hT hfreq XL XR L R z hL hR]

end Ostmann

end OAI
