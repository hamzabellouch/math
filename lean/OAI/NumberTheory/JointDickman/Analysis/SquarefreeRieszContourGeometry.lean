import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszKernel
import OAI.NumberTheory.JointDickman.Analysis.ZetaRectangleLog

namespace OAI

/-! # Interior geometry for the finite squarefree contour -/
namespace JointDickman
open Complex Set

theorem squarefreeRieszKernel_analytic_on_shifted_rectangle {z L δ T : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hδ : δ ≤ 1/4)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ (2*T)))
    {w : ℂ} (hw : 1+w ∈ zetaOpenRectangle δ (2*T)) :
    AnalyticAt ℂ (squarefreeRieszKernel z L f) w := by
  apply squarefreeRieszKernel_analyticAt hz hz1 (hf (1+w) hw)
  have hs : 1-δ < (1+w).re := hw.1.1
  linarith

theorem squarefreeRieszKernel_contour_regular {z L δ c T : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (_hδ : 0 < δ) (hδ4 : δ ≤ 1/4)
    (hc : 0 < c) (hcδ : c ≤ δ/4) (hT : 1 < T)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ (2*T))) :
    DifferentiableOn ℂ (squarefreeRieszKernel z L f)
      (Rectangle (-((δ/4:ℝ):ℂ)-(T:ℂ)*I) ((c:ℂ)+(T:ℂ)*I)) ∧
    ContinuousOn (squarefreeRieszKernel z L f) (Metric.closedBall 0 (3*δ/4)) := by
  constructor
  · intro w hw
    apply (squarefreeRieszKernel_analytic_on_shifted_rectangle hz hz1 hδ4 hf ?_).differentiableAt.differentiableWithinAt
    have hre : (-((δ/4:ℝ):ℂ)-(T:ℂ)*I).re ≤ ((c:ℂ)+(T:ℂ)*I).re := by
      simp only [sub_re,neg_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
        sub_zero,add_re,add_zero]
      linarith
    have him : (-((δ/4:ℝ):ℂ)-(T:ℂ)*I).im ≤ ((c:ℂ)+(T:ℂ)*I).im := by
      simp only [sub_im,neg_im,ofReal_im,mul_im,ofReal_re,I_re,I_im,mul_one,mul_zero,
        zero_add,zero_sub,neg_zero,add_im]
      linarith
    have hmem := (mem_Rect hre him w).mp hw
    simp only [sub_re,neg_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,
      sub_zero,add_re,add_zero,sub_im,neg_im,mul_im,mul_one,zero_add,zero_sub,neg_zero,add_im] at hmem
    change (1-δ < (1+w).re ∧ (1+w).re < 2) ∧ (-(2*T) < (1+w).im ∧ (1+w).im < 2*T)
    simp only [add_re,one_re,add_im,one_im,zero_add]
    constructor <;> constructor <;> linarith [hmem.1,hmem.2.1,hmem.2.2.1,hmem.2.2.2]
  · intro w hw
    apply (squarefreeRieszKernel_analytic_on_shifted_rectangle hz hz1 hδ4 hf ?_).continuousAt.continuousWithinAt
    have hn : ‖w‖ ≤ 3*δ/4 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
    have hre := Complex.abs_re_le_norm w
    have him := Complex.abs_im_le_norm w
    have hr := abs_le.mp (hre.trans hn)
    have hi := abs_le.mp (him.trans hn)
    change (1-δ < (1+w).re ∧ (1+w).re < 2) ∧ (-(2*T) < (1+w).im ∧ (1+w).im < 2*T)
    simp only [add_re,one_re,add_im,one_im,zero_add]
    constructor <;> constructor <;> linarith [hr.1,hr.2,hi.1,hi.2]

end JointDickman

end OAI
