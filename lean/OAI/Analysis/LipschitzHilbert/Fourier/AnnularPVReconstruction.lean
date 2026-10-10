import OAI.Analysis.LipschitzHilbert.Fourier.ScaledConvolutionLimits
import OAI.Analysis.LipschitzHilbert.Fourier.BoundedVerticalMultiplier
import OAI.Analysis.LipschitzHilbert.Fourier.ProductPVVerticalDecay
import OAI.Analysis.LipschitzHilbert.Fourier.SignedAnnularSymbol

namespace OAI

/-! The concrete finite annular convolutions converge pointwise to the
actual principal value. No L2 estimate for that principal value is used. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

def annularPVPartial (N : ℕ) (u : (ℝ×ℝ) → ℝ) (R : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) : (ℝ×ℝ) → ℂ :=
  ∑ n∈Finset.range (2*N+1), verticalConvolution
    (verticalProfileKernel reassemblyDifferenceSchwartz (reassemblyScale N n) 0)
    (productSlopePrincipalValue u R f)

theorem unsignedAnnularSymbol_eq (N : ℕ) :
    signedAnnularSymbol N (fun _ => true)=
      dilatedSlopeWindow reassemblyLow ((16/27)*(2/3:ℝ)^N) (by positivity)-
        dilatedSlopeWindow reassemblyLow ((16/27)*(3/2:ℝ)^(N+1)) (by positivity) := by
  ext x
  simp only [signedAnnularSymbol,ite_true,sum_apply,dilatedSlopeWindow_apply,
    reassemblyDifferenceSchwartz_apply,sub_apply]
  exact reassemblySymbol_eq N x

theorem annularPVPartial_eq (N : ℕ) (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (hub : ∀ z, |u z|≤1) (R : ℝ) (hR : 0<R) (hRs : R≤1/4)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    annularPVPartial N u R f=
      verticalConvolution (verticalProfileKernel reassemblyLow ((16/27)*(2/3:ℝ)^N) 0)
        (productSlopePrincipalValue u R f)-
      verticalConvolution (verticalProfileKernel reassemblyLow ((16/27)*(3/2:ℝ)^(N+1)) 0)
        (productSlopePrincipalValue u R f) := by
  let T := boundedVerticalMultiplierLM 1 (by norm_num) (productSlopePrincipalValue u R f)
    (productSlopePrincipalValue_measurable u hum f f.differentiable R hR hRs)
    (2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ)*R)
    (fun z => productSchwartzPV_pointwise_bound u z (hub z) f R hR)
  have hscale (p : SchwartzMap ℝ ℂ) (d : ℝ) (hd : 0<d) :
      T (dilatedSlopeWindow p d hd.ne')=
        verticalConvolution (verticalProfileKernel p d 0) (productSlopePrincipalValue u R f) := by
    dsimp only [T]
    rw [boundedVerticalMultiplierLM_apply,verticalMultiplier_dilate p d 1 hd (by norm_num),mul_one]
  have hs := congrArg T (unsignedAnnularSymbol_eq N)
  simp only [signedAnnularSymbol,ite_true,map_sum,map_sub] at hs
  simp_rw [hscale reassemblyDifferenceSchwartz _ (reassemblyScale_pos N _),
    hscale reassemblyLow _ (show (0:ℝ)<(16/27)*(2/3:ℝ)^N by positivity),
    hscale reassemblyLow _ (show (0:ℝ)<(16/27)*(3/2:ℝ)^(N+1) by positivity)] at hs
  exact hs

theorem reassemblyLow_kernel_mass : ∫ t, (𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) t=1 := by
  have he : (𝓕 (𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)=reassemblyLow :=
    FourierTransform.fourier_fourierInv_eq reassemblyLow
  have h := congrArg (fun q : SchwartzMap ℝ ℂ => q 0) he
  rw [reassemblyLow_one 0 (by norm_num)] at h
  rw [SchwartzMap.fourier_coe,Real.fourier_eq] at h
  simpa only [Real.inner_apply,mul_zero,neg_zero,Real.fourierChar.map_zero_eq_one,one_smul] using h

theorem annularPVPartial_tendsto (u : (ℝ×ℝ) → ℝ) (hu : Continuous u)
    (hub : ∀ z, |u z|≤1) (R : ℝ) (hR : 0<R) (hRs : R≤1/4)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    Tendsto (fun N => annularPVPartial N u R f z) atTop
      (𝓝 (productSlopePrincipalValue u R f z)) := by
  let F := productSlopePrincipalValue u R f
  let H := fun y : ℝ => F (z.1,y)
  let K : ℝ → ℂ := (𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ)
  let B := 2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ)*R
  have hF : Continuous F := productPV_continuous u hu hub f R hR.le
  have hH : Continuous H := hF.comp (by fun_prop)
  have hb (y : ℝ) : ‖H y‖≤B := productSchwartzPV_pointwise_bound u _ (hub _) f R hR
  have hk : Integrable K := (𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ).integrable
  have hs : Tendsto (fun N : ℕ => (16/27)*(2/3:ℝ)^N) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤2/3)
        (by norm_num : (2/3:ℝ)<1)).const_mul (16/27)
  have hl : Tendsto (fun N : ℕ => (16/27)*(3/2:ℝ)^(N+1)) atTop atTop := by
    have hh := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<3/2)).const_mul_atTop
      (by norm_num : (0:ℝ)<(16/27)*(3/2))
    convert hh using 1
    funext N
    rw [pow_succ]
    ring
  have hsmall := scaledLineConvolution_small K H hk hH.measurable hH B hb
    (fun N => (16/27)*(2/3:ℝ)^N) (fun _ => by positivity) hs z.2
  have hlarge := scaledLineConvolution_large K H hk hH.measurable B hb
    (fun y hy => productPV_vertical_decay u hub f R hR.le z.1 y hy)
    (fun N => (16/27)*(3/2:ℝ)^(N+1)) (fun _ => by positivity) hl z.2
  have hm : (∫ t, K t)*H z.2=F z := by
    rw [show (∫ t, K t)=1 from reassemblyLow_kernel_mass,one_mul]
  rw [hm] at hsmall
  have he (N : ℕ) : annularPVPartial N u R f z=
      lineConvolution (scaledTimeKernel K ((16/27)*(2/3:ℝ)^N)) H z.2-
      lineConvolution (scaledTimeKernel K ((16/27)*(3/2:ℝ)^(N+1))) H z.2 := by
    rw [annularPVPartial_eq N u hu.measurable hub R hR hRs f]
    simp only [Pi.sub_apply,verticalConvolution,verticalProfileKernel,modulatedTimeKernel,
      zero_mul,Real.fourierChar.map_zero_eq_one,one_smul]
    rfl
  simpa only [he,sub_zero] using hsmall.sub hlarge

end LipschitzHilbert.PacketRepresentation

end

end OAI
