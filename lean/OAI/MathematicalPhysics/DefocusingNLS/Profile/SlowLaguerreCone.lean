import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowLaguerreRecurrence
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.TailCone

namespace OAI

/-! # Cone increments for the actual slow-solution coefficients -/

namespace DefocusingNLS

theorem slowLaguerre_cone_increment (q : ℂ) (M : ℕ) (s : ℂ) (n : ℕ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    coneForm M s (slowLaguerreB q (M + 1) s (n + 1))
        (slowLaguerreC q (M + 1) s (n + 1)) -
      coneForm M s (slowLaguerreB q (M + 1) s n) (slowLaguerreC q (M + 1) s n) =
        (q.re + n - M / 2) * Complex.normSq (slowLaguerreCoefficient q (M + 1) s n) := by
  have h := slowLaguerre_recurrence q M s n hq hsre hsim
  rw [slowLaguerreB_succ] at h
  have h' := coneForm_increment (M : ℝ) s (q + n)
    (slowLaguerreB q (M + 1) s n) (slowLaguerreC q (M + 1) s n)
    (slowLaguerreCoefficient q (M + 1) s n) hsre (by simpa using h)
  rw [slowLaguerreC_succ, slowLaguerreB_succ]
  simpa only [Complex.add_re, Complex.natCast_re] using h'

theorem slowLaguerre_mode_cone_increment (σ : ℝ) (ℓ n : ℕ) (q s : ℂ)
    (hσ : -(1 / 32 : ℝ) ≤ σ) (hq : q.re = σ + (ℓ : ℝ) / 2)
    (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    coneForm ((ℓ : ℝ) + 5) s (slowLaguerreB q (ℓ + 6) s (n + 1))
        (slowLaguerreC q (ℓ + 6) s (n + 1)) -
      coneForm ((ℓ : ℝ) + 5) s (slowLaguerreB q (ℓ + 6) s n)
        (slowLaguerreC q (ℓ + 6) s n) =
        (σ + n - 5 / 2) * Complex.normSq (slowLaguerreCoefficient q (ℓ + 6) s n) := by
  have hq' : -1 < q.re := by rw [hq]; linarith [Nat.cast_nonneg (α := ℝ) ℓ]
  have h := slowLaguerre_cone_increment q (ℓ + 5) s n hq' hsre hsim
  have he : ℓ + 5 + 1 = ℓ + 6 := by omega
  rw [he] at h
  push_cast at h
  rw [hq] at h
  convert h using 1
  ring

end DefocusingNLS

end OAI
