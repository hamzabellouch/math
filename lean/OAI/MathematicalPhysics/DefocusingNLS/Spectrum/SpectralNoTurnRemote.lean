import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnGeometry
import Mathlib.Analysis.Real.Sqrt

namespace OAI

/-! In the bounded angular-ratio regime, the remote radius is comparable
to the square root of the imaginary spectral parameter. -/

namespace DefocusingNLS

theorem spectralNoTurn_remote (ell : ℕ) (omega C R E : ℝ)
    (hC : 0 ≤ C) (hw : C+2 ≤ omega) (hR : 0 < R) (hRw : R^2 ≤ omega)
    (hL : (ell : ℝ)*(ell+10)+99/4 ≤ C*omega)
    (hE : 0 < E) (hEs : E^2 = 256*max ((ell : ℝ)+1) omega) :
    R ≤ E ∧ E ≤ 32*Real.sqrt (omega/2) := by
  have hwp : 0 < omega := by linarith
  have hell : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
  have hdom : (ell : ℝ)+1 ≤ omega := by
    by_contra hn
    have hgt : omega-1 < (ell : ℝ) := by linarith
    have hsq : (omega-1)^2 < (ell : ℝ)^2 := by nlinarith
    have hnon := mul_nonneg hwp.le (sub_nonneg.mpr hw)
    nlinarith
  rw [max_eq_right hdom] at hEs
  have hroot : (Real.sqrt (omega/2))^2 = omega/2 := Real.sq_sqrt (by positivity)
  have hr0 := Real.sqrt_nonneg (omega/2)
  constructor
  · nlinarith [sq_nonneg R]
  · nlinarith

end DefocusingNLS

end OAI
