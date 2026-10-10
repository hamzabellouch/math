import OAI.Probability.SLE.Geometry.RectangleWedgeSplit

namespace OAI

/-! Boundary-integral control on a closed rectangle. -/
noncomputable section
open Complex MeasureTheory Set
open scoped Topology Interval

namespace SLEExactGauge

lemma rectangle_vertical_integrable {f : ℂ → ℂ} {z w : ℂ}
    (hC : ContinuousOn f (Rectangle z w)) {x : ℝ} (hx : x∈uIcc z.re w.re) :
    IntervalIntegrable (fun y : ℝ => f (x+y*I)) volume z.im w.im := by
  apply ContinuousOn.intervalIntegrable
  apply hC.comp (continuous_const.add (continuous_ofReal.mul_const I)).continuousOn
  intro y hy
  change (x+(y:ℂ)*I).re∈uIcc z.re w.re ∧ (x+(y:ℂ)*I).im∈uIcc z.im w.im
  simpa only [add_re,add_im,ofReal_re,ofReal_im,mul_re,mul_im,I_re,I_im,
    mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add] using And.intro hx hy

lemma rectangle_wedge_split_of_continuous {f : ℂ → ℂ} {z w : ℂ}
    (hC : ContinuousOn f (Rectangle z w)) {c : ℝ} (hc : c∈uIcc z.im w.im) :
    wedgeIntegral z w f+wedgeIntegral w z f=
      (wedgeIntegral z (⟨w.re,c⟩:ℂ) f+wedgeIntegral (⟨w.re,c⟩:ℂ) z f)+
      (wedgeIntegral (⟨z.re,c⟩:ℂ) w f+wedgeIntegral w (⟨z.re,c⟩:ℂ) f) := by
  have hz := (IntervalIntegrable.trans_iff hc).mp
    (rectangle_vertical_integrable hC (left_mem_uIcc : z.re∈uIcc z.re w.re))
  have hw := (IntervalIntegrable.trans_iff hc).mp
    (rectangle_vertical_integrable hC (right_mem_uIcc : w.re∈uIcc z.re w.re))
  exact rectangle_wedge_split f z w c hz.1 hz.2 hw.1 hw.2

lemma rectangle_wedge_eq_zero {f : ℂ → ℂ} {z w : ℂ}
    (hC : ContinuousOn f (Rectangle z w))
    (hD : DifferentiableOn ℂ f
      (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im))) :
    wedgeIntegral z w f+wedgeIntegral w z f=0 := by
  rw [wedgeIntegral_add_wedgeIntegral_eq]
  exact integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w hC hD

end SLEExactGauge

end

end OAI
