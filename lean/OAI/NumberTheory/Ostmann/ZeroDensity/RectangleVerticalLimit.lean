import OAI.NumberTheory.Ostmann.ZeroDensity.GaussianContourShift

namespace OAI

/-! # Passing a zero rectangle identity to its two convergent vertical lines -/

namespace Ostmann

open Complex Filter MeasureTheory
open scoped Topology Interval

 theorem rectangle_vertical_limit (f : ℂ → ℂ) (a b : ℝ)
    (ha : Integrable (fun u : ℝ => f ((a : ℂ) + u * I)))
    (hb : Integrable (fun u : ℝ => f ((b : ℂ) + u * I)))
    (ht : Tendsto (fun u : ℝ => ∫ x in a..b, f ((x : ℂ) + u * I)) atTop (𝓝 0))
    (hd : Tendsto (fun u : ℝ => ∫ x in a..b, f ((x : ℂ) + (-u) * I)) atTop (𝓝 0))
    (hz : ∀ᶠ T : ℝ in atTop, rectangleBoundaryIntegral f a b (-T) T = 0) :
    (∫ u : ℝ, f ((a : ℂ) + u * I)) = ∫ u : ℝ, f ((b : ℂ) + u * I) := by
  have hr := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hl := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hbd : Tendsto (fun T : ℝ => rectangleBoundaryIntegral f a b (-T) T) atTop
      (𝓝 (I * (∫ u : ℝ, f ((b : ℂ) + u * I)) - I * ∫ u : ℝ, f ((a : ℂ) + u * I))) := by
    simpa [rectangleBoundaryIntegral] using ((hd.sub ht).add (hr.const_mul I)).sub (hl.const_mul I)
  have hzero : Tendsto (fun T : ℝ => rectangleBoundaryIntegral f a b (-T) T) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hz.mono fun _ h => h.symm)
  have he := tendsto_nhds_unique hbd hzero
  exact (mul_left_cancel₀ I_ne_zero (sub_eq_zero.mp he)).symm

end Ostmann

end OAI
