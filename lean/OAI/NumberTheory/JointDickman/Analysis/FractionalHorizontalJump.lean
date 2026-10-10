import OAI.NumberTheory.JointDickman.Analysis.FractionalContourRectangles
import OAI.NumberTheory.JointDickman.Analysis.FractionalPositiveIntegral

namespace OAI

/-! # The horizontal contour jump is the local Hankel integral -/
namespace JointDickman
open Filter Set MeasureTheory Complex
open scoped Topology

theorem fractionalContour_horizontal_split {z η c R ε : ℝ}
    (hη : 0 < η) (hc : 0 < c) (hcη : c ≤ η) (hR : 2*η < R)
    (hε : ε ≠ 0) (hεη : |ε| < η) {F : ℂ → ℂ}
    (hF : ContinuousOn F (Metric.closedBall 0 R)) :
    HIntegral (fractionalContourIntegrand z F) (-η) c ε =
      (∫ t : ℝ in Ioc 0 η, F (-(t:ℂ)+(ε:ℂ)*I)*fractionalPowerKernel z (-(t:ℂ)+(ε:ℂ)*I)) +
      (∫ t : ℝ in Ioc 0 c, F ((t:ℂ)+(ε:ℂ)*I)*fractionalPowerKernel z ((t:ℂ)+(ε:ℂ)*I)) := by
  have hηc : -η ≤ c := by linarith
  have hpath : Continuous (fun t : ℝ => (t:ℂ)+(ε:ℂ)*I) := by fun_prop
  have hmap (t : ℝ) (ht : t ∈ Icc (-η) c) :
      (t:ℂ)+(ε:ℂ)*I ∈ Metric.closedBall 0 R := by
    rw [Metric.mem_closedBall,dist_zero_right]
    have htη : |t| ≤ η := abs_le.mpr ⟨ht.1,ht.2.trans hcη⟩
    calc
      _ ≤ ‖(t:ℂ)‖+‖(ε:ℂ)*I‖ := norm_add_le _ _
      _ = |t|+|ε| := by simp
      _ ≤ R := by linarith
  have hcon : ContinuousOn (fun t : ℝ => fractionalContourIntegrand z F ((t:ℂ)+(ε:ℂ)*I))
      (Icc (-η) c) := by
    apply (hF.comp' hpath.continuousOn hmap).mul
    intro t _
    apply (ContinuousAt.comp (f := fun t : ℝ => (t:ℂ)+(ε:ℂ)*I)
      (fractionalPower_differentiableAt z (Or.inr (by simpa using hε))).continuousAt
      hpath.continuousAt).continuousWithinAt
  have hi := hcon.intervalIntegrable_of_Icc (μ := volume) hηc
  have h0 : (0:ℝ) ∈ uIcc (-η) c := by rw [uIcc_of_le hηc]; exact ⟨by linarith,hc.le⟩
  have his := (IntervalIntegrable.trans_iff h0).mp hi
  rw [HIntegral,←intervalIntegral.integral_add_adjacent_intervals his.1 his.2]
  congr 1
  · have hn := intervalIntegral.integral_comp_neg (fun t : ℝ =>
        fractionalContourIntegrand z F ((t:ℂ)+(ε:ℂ)*I)) (a := 0) (b := η)
    simp only [neg_zero] at hn
    rw [←hn]
    simp only [intervalIntegral.integral_of_le hη.le,Complex.ofReal_neg,
      fractionalContourIntegrand]
  · rw [intervalIntegral.integral_of_le hc.le]
    rfl

theorem fractionalContour_horizontal_jump {z η c R : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (hη : 0 < η) (hc : 0 < c) (hcη : c ≤ η)
    (hR : 2*η < R) {F : ℂ → ℂ} (hF : ContinuousOn F (Metric.closedBall 0 R)) :
    Tendsto (fun ε : ℝ => (1/(2*(Real.pi:ℂ)*I)) *
      (HIntegral (fractionalContourIntegrand z F) (-η) c (-ε) -
       HIntegral (fractionalContourIntegrand z F) (-η) c ε))
      (𝓝[>] 0) (𝓝 ((Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 η, (t^(-z):ℝ) • F (-(t:ℂ))))) := by
  have hp := fractionalPositive_integral hz hz1 hc (lt_of_le_of_lt (by linarith) hR) hF
  have hpu := hp.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have hneg : Tendsto (fun ε : ℝ => -ε) (𝓝[>] 0) (𝓝 0) := by
    simpa only [neg_zero] using (continuous_neg.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
  have hpl := hp.comp hneg
  have hzero := ((hpl.sub hpu).const_mul (1/(2*(Real.pi:ℂ)*I)))
  simp only [sub_self,mul_zero] at hzero
  have hsum := (fractionalCut_jump_integral hz hz1 hη hR hF).add hzero
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
  rw [fractionalContour_horizontal_split hη hc hcη hR (neg_ne_zero.mpr hε.1.ne')
      (by simpa [abs_of_pos hε.1] using hε.2) hF,
    fractionalContour_horizontal_split hη hc hcη hR hε.1.ne'
      (by simpa [abs_of_pos hε.1] using hε.2) hF]
  simp only [Complex.ofReal_neg,Function.comp_apply]
  simp only [sub_eq_add_neg]
  ring_nf

end JointDickman

end OAI
