import OAI.NumberTheory.Ostmann.Characters.MixedExternalMass

namespace OAI

/-! # Bounded invariant giant factors do not enlarge the symmetrized energy -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedBulkSymmetrize_bounded_statistic_cauchy {B A : Type*} [Fintype B] [Fintype A]
    (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (hidentical : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ)
    (F H P : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (hH : ∀ e s y x z, H s (selectedBulkSample slot e y) x z = H s y x z)
    (hP : ∀ e s y x z, P s (selectedBulkSample slot e y) x z = P s y x z)
    (hPnorm : ∀ s y x z, ‖P s y x z‖ ≤ 1)
    (W : ℝ → ℝ → ℝ) (hW : ∀ x z, 0 ≤ W x z) :
    ‖mixedExternalAverage ν N u v r w center
      (fun s y x z => ((P s y x z * H s y x z) * F s y x z) * W x z)‖ ^ 2 ≤
    (mixedExternalAverage ν N u v r w center (fun _ _ x z => (W x z : ℂ))).re *
    (mixedExternalAverage ν N u v r w center (fun s y x z =>
      (‖mixedBulkSymmetrize n m slot F s y x z‖ ^ 2 : ℂ) *
        ((W x z : ℂ) * (‖H s y x z‖ ^ 2 : ℝ)))).re := by
  have hc := mixedBulkSymmetrize_statistic_cauchy n m slot ν hν hidentical N
    u v r w center F (fun s y x z => P s y x z * H s y x z)
    (fun e s y x z => by rw [hP, hH]) W hW
  apply hc.trans
  apply mul_le_mul_of_nonneg_left
  · apply mixedExternalAverage_re_mono ν hν N u v r w center
    intro s y x z
    simp only [norm_mul, mul_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    have hp : ‖P s y x z‖ ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hPnorm s y x z) 2
    have hscale : 0 ≤ ‖mixedBulkSymmetrize n m slot F s y x z‖ ^ 2 * W x z := by
      exact mul_nonneg (sq_nonneg _) (hW x z)
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hp (sq_nonneg ‖H s y x z‖)) hscale
    nlinarith
  · exact mixedExternalAverage_re_nonneg ν hν N u v r w center _
      (fun _ _ x z => by simpa only [Complex.ofReal_re] using hW x z)

end Ostmann

end OAI
