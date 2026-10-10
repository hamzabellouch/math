import OAI.NumberTheory.TwoPoint.Fourier.ModFiveRightBound
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrincipalCorrection

namespace OAI

/-! Absolute convergence gives the zeta logarithmic derivative bound on
any right line. The modulus-five estimate differs by one bounded Euler factor. -/

namespace TwoPointCorrelations

open Complex

theorem mrt_zeta_logderiv_right_bound : ∃ C : ℝ, 0 < C ∧
    ∀ δ t : ℝ, 0 < δ →
      ‖deriv riemannZeta (((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta (((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 / δ + C := by
  obtain ⟨C, hC, hb⟩ := modFive_logderiv_right_bound
  refine ⟨C + Real.log 5, by positivity, ?_⟩
  intro δ t hδ
  let s : ℂ := (((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  have hs : 1 < s.re := by simpa [s] using hδ
  have he := mrt_principal_logderiv_error (q := 5) hs
  norm_num only [Nat.cast_ofNat] at he
  have hh := hb (1 : DirichletCharacter ℂ 5) δ t hδ
  have hnorm : ‖logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 5)) s‖ ≤
      1 / δ + C := by
    simpa only [logDeriv_apply, neg_div, norm_neg] using hh
  have hx := norm_sub_le (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 5)) s)
    (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 5)) s - logDeriv riemannZeta s)
  rw [sub_sub_cancel] at hx
  change ‖logDeriv riemannZeta s‖ ≤ _
  linarith

end TwoPointCorrelations

end OAI
