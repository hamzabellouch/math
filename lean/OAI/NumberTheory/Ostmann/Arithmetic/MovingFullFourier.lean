import OAI.NumberTheory.Ostmann.Arithmetic.MovingFourierSupported
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFourierBudget
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSpectatorProduct

namespace OAI

/-! # The full supported coefficient with its explicit polynomial smooth part -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- The actual full integrand separates into its original support coefficient,
the constructed Fourier polynomials, and the actual moving spectator trees.
This includes every zero-support term. -/
theorem moving_full_fourier_decomposition {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (hextra : ∀ i x s v w, extra x s v w ≠ 0 →
      (historyPivot (movingSlotSystem value childBound pivotBound) x s v w : ZMod (q i)) ≠ 0)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hfreq : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (L R : Polynomial ℝ) (z : ℝ)
    (hL : L.eval z = (XL : ℝ)) (hR : R.eval z = (XR : ℝ)) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => (movingWindowLeaf value X lo hi F x s * movingFourierLeaf value ψ X x s) *
          ∏ i ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g i) (D i) x s)
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t =
      (recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (movingWindowLeaf value X lo hi F) (movingSlotCutoff value childBound pivotBound extra)
        n ⟨n, T, XL, XR⟩ t *
          smoothPolynomialWeight (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi) z) *
        ∏ i ∈ S, movingSlotSpectator value (g i) (D i) T XL XR := by
  rw [movingSlotWeight_spectator_product q value childBound pivotBound _ extra hextra
    g D S T t hT XL XR]
  rw [moving_windowed_fourier_polynomial value hvalue childBound pivotBound F extra
    ψ X lo hi hlo hhi T t hT hfreq XL XR L R z hL hR]

end Ostmann

end OAI
