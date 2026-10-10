import OAI.Analysis.LipschitzHilbert.Estimates.TimeEndpointComparison
import OAI.Analysis.LipschitzHilbert.Fourier.DominatedKernelAverage
import OAI.Analysis.LipschitzHilbert.Estimates.ShortSlopeLp

namespace OAI

/-! A measurable factor between one half and one may change both sharp
endpoints. The resulting kernel error has a uniform integrable majorant. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_close_upper (r R S t : ℝ) (hR : 0<R)
    (hRS : R≤S) (hSR : S≤2*R) :
    ‖sharpTimeKernel r R t-sharpTimeKernel r S t‖≤3*timeErrorEnvelope R t := by
  have hq := timeErrorEnvelope_nonneg R t hR
  by_cases hr : r< |t|
  · by_cases htR : |t|<R
    · have htS : |t|<S := htR.trans_le hRS
      simp only [sharpTimeKernel, hr, htR, htS, and_self, ite_true, sub_self, norm_zero]
      positivity
    · by_cases htS : |t|<S
      · have ht : 0< |t| := hR.trans_le (le_of_not_gt htR)
        have ht2 : |t|≤2*R := htS.le.trans hSR
        have hd : 0<R^2+t^2 := by positivity
        have hpoly : R^2+t^2≤3*R*|t| := by
          nlinarith [sq_abs t,mul_nonneg (sub_nonneg.mpr (le_of_not_gt htR))
            (sub_nonneg.mpr ht2)]
        simp only [sharpTimeKernel,hr,htR,htS,true_and,ite_true,ite_false,
          zero_sub,norm_neg,norm_inv,Complex.norm_real,Real.norm_eq_abs,timeErrorEnvelope]
        rw [←mul_div_assoc,inv_eq_one_div]
        apply (div_le_div_iff₀ ht hd).2
        nlinarith only [hpoly]
      · simp only [sharpTimeKernel,hr,htR,htS,true_and,ite_false,sub_self,norm_zero]
        positivity
  · simp only [sharpTimeKernel,hr,false_and,ite_false,sub_self,norm_zero]
    positivity

def endpointErrorMajorant (epsilon R t : ℝ) : ℝ :=
  6*timeErrorEnvelope (epsilon/2) t+6*timeErrorEnvelope (R/2) t

theorem endpointErrorMajorant_nonneg (epsilon R t : ℝ) (he : 0<epsilon) (hR : 0<R) :
    0≤endpointErrorMajorant epsilon R t := by
  exact add_nonneg (mul_nonneg (by norm_num) (timeErrorEnvelope_nonneg _ _ (by linarith)))
    (mul_nonneg (by norm_num) (timeErrorEnvelope_nonneg _ _ (by linarith)))

theorem endpointErrorMajorant_measurable (epsilon R : ℝ) :
    Measurable (endpointErrorMajorant epsilon R) := by
  unfold endpointErrorMajorant timeErrorEnvelope
  fun_prop

theorem endpointErrorMajorant_integrable (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R) :
    Integrable (endpointErrorMajorant epsilon R) :=
  ((timeErrorEnvelope_integrable _ (by linarith)).const_mul 6).add
    ((timeErrorEnvelope_integrable _ (by linarith)).const_mul 6)

theorem endpointErrorMajorant_integral (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R) :
    (∫ t, endpointErrorMajorant epsilon R t)=12*Real.pi := by
  change (∫ t, 6*timeErrorEnvelope (epsilon/2) t+6*timeErrorEnvelope (R/2) t)=_
  rw [integral_add
    ((timeErrorEnvelope_integrable _ (by linarith)).const_mul 6)
    ((timeErrorEnvelope_integrable _ (by linarith)).const_mul 6)]
  simp only [integral_const_mul, timeErrorEnvelope_integral _ (by linarith : 0<epsilon/2),
    timeErrorEnvelope_integral _ (by linarith : 0<R/2)]
  ring

theorem sharpTimeKernel_scaled_diff (epsilon R a t : ℝ)
    (he : 0<epsilon) (hR : 0<R) (ha : 1/2≤a) (ha1 : a≤1) :
    ‖sharpTimeKernel (epsilon*a) (R*a) t-sharpTimeKernel epsilon R t‖≤
      endpointErrorMajorant epsilon R t := by
  have h1 := sharpTimeKernel_close_lower (epsilon/2) (epsilon*a) (R*a) t
    (by linarith) (by nlinarith) (by nlinarith)
  have h2 := sharpTimeKernel_close_upper (epsilon/2) (R/2) (R*a) t
    (by linarith) (by nlinarith) (by nlinarith)
  have h3 := sharpTimeKernel_close_upper (epsilon/2) (R/2) R t
    (by linarith) (by linarith) (by linarith)
  have h4 := sharpTimeKernel_close_lower (epsilon/2) epsilon R t
    (by linarith) (by linarith) (by linarith)
  have heq : sharpTimeKernel (epsilon*a) (R*a) t-sharpTimeKernel epsilon R t=
      (sharpTimeKernel (epsilon*a) (R*a) t-sharpTimeKernel (epsilon/2) (R*a) t)+
      (sharpTimeKernel (epsilon/2) (R*a) t-sharpTimeKernel (epsilon/2) (R/2) t)+
      (sharpTimeKernel (epsilon/2) (R/2) t-sharpTimeKernel (epsilon/2) R t)+
      (sharpTimeKernel (epsilon/2) R t-sharpTimeKernel epsilon R t) := by ring
  rw [norm_sub_rev] at h1 h2
  rw [heq]
  have hn := norm_add_le
    ((sharpTimeKernel (epsilon*a) (R*a) t-sharpTimeKernel (epsilon/2) (R*a) t)+
      (sharpTimeKernel (epsilon/2) (R*a) t-sharpTimeKernel (epsilon/2) (R/2) t)+
      (sharpTimeKernel (epsilon/2) (R/2) t-sharpTimeKernel (epsilon/2) R t))
    (sharpTimeKernel (epsilon/2) R t-sharpTimeKernel epsilon R t)
  have hn2 := norm_add_le
    ((sharpTimeKernel (epsilon*a) (R*a) t-sharpTimeKernel (epsilon/2) (R*a) t)+
      (sharpTimeKernel (epsilon/2) (R*a) t-sharpTimeKernel (epsilon/2) (R/2) t))
    (sharpTimeKernel (epsilon/2) (R/2) t-sharpTimeKernel (epsilon/2) R t)
  have hn3 := norm_add_le
    (sharpTimeKernel (epsilon*a) (R*a) t-sharpTimeKernel (epsilon/2) (R*a) t)
    (sharpTimeKernel (epsilon/2) (R*a) t-sharpTimeKernel (epsilon/2) (R/2) t)
  unfold endpointErrorMajorant
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
