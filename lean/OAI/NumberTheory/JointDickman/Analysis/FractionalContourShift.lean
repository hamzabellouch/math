import OAI.NumberTheory.JointDickman.Analysis.FractionalHorizontalJump
import OAI.NumberTheory.JointDickman.Analysis.FractionalVerticalIntegral

namespace OAI

/-! # Exact finite contour shift through an integrable fractional pole -/
namespace JointDickman
open Filter Set MeasureTheory Complex
open scoped Topology

theorem fractionalContourShift_of_integrable {z η c T R : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (hη : 0 < η) (hc : 0 < c)
    (hcη : c ≤ η) (hT : 0 < T) (hR : 2*η < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Rectangle (-(η:ℂ)-(T:ℂ)*I) ((c:ℂ)+(T:ℂ)*I)))
    (hFlocal : ContinuousOn F (Metric.closedBall 0 R))
    (hleft : IntervalIntegrable (fun t : ℝ => fractionalContourIntegrand z F (-(η:ℂ)+(t:ℂ)*I)) volume (-T) T)
    (hright : IntervalIntegrable (fun t : ℝ => fractionalContourIntegrand z F ((c:ℂ)+(t:ℂ)*I)) volume (-T) T) :
    (1/(2*(Real.pi:ℂ)*I)) * VIntegral (fractionalContourIntegrand z F) c (-T) T =
      (1/(2*(Real.pi:ℂ)*I)) *
        (VIntegral (fractionalContourIntegrand z F) (-η) (-T) T +
         HIntegral (fractionalContourIntegrand z F) (-η) c T -
         HIntegral (fractionalContourIntegrand z F) (-η) c (-T)) +
      (Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 η, (t^(-z):ℝ) • F (-(t:ℂ))) := by
  have hvl := VIntegral_remove_middle_gap (x := -η) hT (by simpa only [ofReal_neg] using hleft)
  have hvr := VIntegral_remove_middle_gap hT hright
  have hlim := (((hvr.sub hvl).sub_const
    (HIntegral (fractionalContourIntegrand z F) (-η) c T -
      HIntegral (fractionalContourIntegrand z F) (-η) c (-T))).const_mul (1/(2*(Real.pi:ℂ)*I)))
  have hj := fractionalContour_horizontal_jump hz hz1 hη hc hcη hR hFlocal
  have he : (fun ε : ℝ => (1/(2*(Real.pi:ℂ)*I)) *
      ((VIntegral (fractionalContourIntegrand z F) c ε T +
        VIntegral (fractionalContourIntegrand z F) c (-T) (-ε)) -
       (VIntegral (fractionalContourIntegrand z F) (-η) ε T +
        VIntegral (fractionalContourIntegrand z F) (-η) (-T) (-ε)) -
       (HIntegral (fractionalContourIntegrand z F) (-η) c T -
        HIntegral (fractionalContourIntegrand z F) (-η) c (-T)))) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => (1/(2*(Real.pi:ℂ)*I)) *
        (HIntegral (fractionalContourIntegrand z F) (-η) c (-ε) -
         HIntegral (fractionalContourIntegrand z F) (-η) c ε)) := by
    filter_upwards [Ioo_mem_nhdsGT hT] with ε hε
    have heq := fractionalContour_rectangles (z := z) hη hc hε.1 hε.2 hF
    rw [heq]
    ring
  have hv := tendsto_nhds_unique hlim (hj.congr' he.symm)
  calc
    _ = (1/(2*(Real.pi:ℂ)*I)) *
          (VIntegral (fractionalContourIntegrand z F) (-η) (-T) T +
           HIntegral (fractionalContourIntegrand z F) (-η) c T -
           HIntegral (fractionalContourIntegrand z F) (-η) c (-T)) +
        (1/(2*(Real.pi:ℂ)*I)) *
          (VIntegral (fractionalContourIntegrand z F) c (-T) T -
           VIntegral (fractionalContourIntegrand z F) (-η) (-T) T -
           (HIntegral (fractionalContourIntegrand z F) (-η) c T -
            HIntegral (fractionalContourIntegrand z F) (-η) c (-T))) := by ring
    _ = _ := by rw [hv]

theorem fractionalContourShift {z η c T R : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (hη : 0 < η) (hc : 0 < c)
    (hcη : c ≤ η) (hT : 0 < T) (hR : 2*η < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Rectangle (-(η:ℂ)-(T:ℂ)*I) ((c:ℂ)+(T:ℂ)*I)))
    (hFlocal : ContinuousOn F (Metric.closedBall 0 R)) :
    (1/(2*(Real.pi:ℂ)*I)) * VIntegral (fractionalContourIntegrand z F) c (-T) T =
      (1/(2*(Real.pi:ℂ)*I)) *
        (VIntegral (fractionalContourIntegrand z F) (-η) (-T) T +
         HIntegral (fractionalContourIntegrand z F) (-η) c T -
         HIntegral (fractionalContourIntegrand z F) (-η) c (-T)) +
      (Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 η, (t^(-z):ℝ) • F (-(t:ℂ))) := by
  have hline (x : ℝ) (hx : -η ≤ x ∧ x ≤ c) :
      ContinuousOn (fun t : ℝ => F ((x:ℂ)+(t:ℂ)*I)) (Icc (-T) T) := by
    have hp : Continuous (fun t : ℝ => (x:ℂ)+(t:ℂ)*I) := by fun_prop
    apply hF.continuousOn.comp' hp.continuousOn
    intro t ht
    have hRe : (-(η:ℂ)-(T:ℂ)*I).re ≤ ((c:ℂ)+(T:ℂ)*I).re := by
      simp only [sub_re,neg_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
        sub_zero,add_re,add_zero]
      linarith
    have hIm : (-(η:ℂ)-(T:ℂ)*I).im ≤ ((c:ℂ)+(T:ℂ)*I).im := by
      simp only [sub_im,neg_im,ofReal_im,mul_im,ofReal_re,I_re,I_im,mul_one,mul_zero,
        zero_add,zero_sub,neg_zero,add_im]
      linarith
    apply (mem_Rect hRe hIm _).mpr
    simpa only [sub_re,neg_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
      sub_zero,add_re,add_zero,sub_im,neg_im,mul_im,mul_one,zero_add,zero_sub,neg_zero,add_im]
      using And.intro hx.1 (And.intro hx.2 (And.intro ht.1 ht.2))
  have hleft : IntervalIntegrable
      (fun t : ℝ => fractionalContourIntegrand z F ((-η:ℝ)+(t:ℂ)*I)) volume (-T) T := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -T ≤ T)).mpr
    exact fractionalContour_vertical_integrable hz (neg_ne_zero.mpr hη.ne')
      (hline (-η) ⟨le_rfl,by linarith⟩)
  have hright : IntervalIntegrable
      (fun t : ℝ => fractionalContourIntegrand z F ((c:ℂ)+(t:ℂ)*I)) volume (-T) T := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -T ≤ T)).mpr
    exact fractionalContour_vertical_integrable hz hc.ne' (hline c ⟨by linarith,le_rfl⟩)
  apply fractionalContourShift_of_integrable hz hz1 hη hc hcη hT hR hF hFlocal
  · simpa only [Complex.ofReal_neg] using hleft
  · exact hright

end JointDickman

end OAI
