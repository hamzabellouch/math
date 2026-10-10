import OAI.NumberTheory.Ostmann.ZeroDensity.RieszMellinKernel

namespace OAI

/-! # Mellin inversion for the one-sided Riesz weight -/

namespace Ostmann

open Complex MeasureTheory

theorem rieszMellinKernel_verticalIntegrable (σ : ℝ) (hσ : 1 ≤ σ) :
    Complex.VerticalIntegrable rieszMellinKernel σ := by
  have hmajor : Integrable (fun t : ℝ => 4 * (1 + ‖t‖) ^ (-(2 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2)).const_mul 4
  have hc : Continuous (fun t : ℝ => rieszMellinKernel ((σ : ℂ) + (t : ℂ) * I)) := by
    unfold rieszMellinKernel
    apply continuous_const.div
    · fun_prop
    · intro t
      apply mul_ne_zero
      · intro h
        have hh := congrArg Complex.re h
        simp at hh
        linarith
      · intro h
        have hh := congrArg Complex.re h
        simp at hh
        linarith
  apply hmajor.mono' hc.aestronglyMeasurable
  filter_upwards with t
  simpa only [Real.norm_eq_abs] using rieszMellinKernel_line_bound σ t hσ

theorem rieszPrimeTest_mellin_inversion (σ x : ℝ) (hσ : 1 ≤ σ) (hx : 0 < x) :
    mellinInv σ rieszMellinKernel x = rieszPrimeTest x := by
  have hσp : 0 < σ := by linarith
  have hF : Complex.VerticalIntegrable (mellin rieszPrimeTest) σ := by
    have hfun : (fun t : ℝ => mellin rieszPrimeTest ((σ : ℂ) + (t : ℂ) * I)) =
        (fun t : ℝ => rieszMellinKernel ((σ : ℂ) + (t : ℂ) * I)) := by
      funext t
      exact (rieszPrimeTest_hasMellin _ (by simpa using hσp)).2
    change Integrable (fun t : ℝ => mellin rieszPrimeTest ((σ : ℂ) + (t : ℂ) * I))
    rw [hfun]
    exact rieszMellinKernel_verticalIntegrable σ hσ
  have hi := mellinInv_mellin_eq σ rieszPrimeTest hx
    (rieszPrimeTest_hasMellin (σ : ℂ) hσp).1 hF rieszPrimeTest_continuous.continuousAt
  rw [← hi]
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [(rieszPrimeTest_hasMellin ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσp)).2]

end Ostmann

end OAI
