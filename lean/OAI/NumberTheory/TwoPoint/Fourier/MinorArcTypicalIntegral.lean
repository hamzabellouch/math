import OAI.NumberTheory.TwoPoint.Fourier.MinorArcRamareWindow
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcShortError

namespace OAI

/-! The actual typical-set short-sum integral, reduced to the bounded
bilinear window plus its single prime-square error. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem minor_arc_typical_integral_le {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    (X H M : ℕ) (hM : ∀ p ∈ P j, ∀ k ∈ range X, (k + H) / p < M) (α : ℝ) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H α ≤
      (∑ k ∈ range X, ‖minorArcBilinearWindow (P j) M H 1
        (minorArcRamareCofactor (P j) (mrtTypicalCoefficient (J.erase j) P F)) F α k‖) +
        3 * (H : ℝ) * (X + H) * ∑ p ∈ P j, 1 / (p : ℝ) ^ 2 := by
  let C := mrtTypicalCoefficient J P F
  let B := mrtTypicalCoefficient (J.erase j) P F
  let A := minorArcRamareApprox (P j) F B
  let E := fun n => C n - A n
  have herr : (∑ k ∈ range X, ‖shortExponentialSum E H α k‖) ≤
      3 * (H : ℝ) * (X + H) * ∑ p ∈ P j, 1 / (p : ℝ) ^ 2 := by
    apply minor_arc_short_square_error (P j) (hP j hj) E X H 3 (by norm_num)
    intro n hn _
    exact minor_arc_typical_ramare_pointwise J P hP hdis hj F hF hFb hn
  have hlin (k : ℕ) : shortExponentialSum C H α k =
      shortExponentialSum A H α k + shortExponentialSum E H α k := by
    simp only [shortExponentialSum_at_nat]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    dsimp [E]
    ring
  rw [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ k ∈ range X, (‖shortExponentialSum A H α k‖ +
        ‖shortExponentialSum E H α k‖) := by
      apply sum_le_sum
      intro k _
      rw [show mrtTypicalCoefficient J P F = C from rfl, hlin]
      exact norm_add_le _ _
    _ = (∑ k ∈ range X, ‖minorArcBilinearWindow (P j) M H 1
          (minorArcRamareCofactor (P j) B) F α k‖) +
        ∑ k ∈ range X, ‖shortExponentialSum E H α k‖ := by
      rw [sum_add_distrib]
      congr 1
      apply sum_congr rfl
      intro k hk
      exact congrArg norm (minor_arc_ramare_short_eq_bounded (P j) M H k
        (fun p hp => (hP j hj p hp).pos) (fun p hp => hM p hp k hk) F B α)
    _ ≤ _ := add_le_add le_rfl herr

end TwoPointCorrelations

end OAI
