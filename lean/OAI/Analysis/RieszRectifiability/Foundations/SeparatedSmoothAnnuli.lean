import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.SmoothAnnularWeights

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric

theorem smoothAnnularWeight_nonneg_of_separated {d : ℕ}
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (hsep : 2 * r ≤ R)
    (x : Ambient d) : 0 ≤ smoothAnnularWeight a r R hr hR x := by
  have hb := annularSmoothBallCutoff_basic a r hr
  have hB := annularSmoothBallCutoff_basic a R hR
  unfold smoothAnnularWeight
  by_cases hx : dist x a ≤ R
  · rw [hB.2.2.1 x hx]
    exact sub_nonneg.mpr (annularSmoothBallCutoff a r hr).le_one
  · rw [hb.2.2.2 x (hsep.trans (le_of_not_ge hx))]
    simpa only [sub_zero] using! (annularSmoothBallCutoff a R hR).nonneg (x := x)

theorem smoothAnnularWeight_eq_one_on_middle {d : ℕ}
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (x : Ambient d) (hinner : 2 * r ≤ dist x a) (houter : dist x a ≤ R) :
    smoothAnnularWeight a r R hr hR x = 1 := by
  have hb := annularSmoothBallCutoff_basic a r hr
  have hB := annularSmoothBallCutoff_basic a R hR
  rw [smoothAnnularWeight, hB.2.2.1 x houter, hb.2.2.2 x hinner, sub_zero]

end

end RieszRectifiability

end OAI
