import OAI.NumberTheory.CubicMoment.Theta.CubicThetaWindowProfile
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! The radial Green flux of the actual compact incoming window. -/
noncomputable section
open Set Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaWindowFlux (v : ℝ) : ℂ :=
  (v:ℂ)^(-1/3:ℂ)*deriv (cubicThetaWindowHeight (4/3)) v -
    (2/3:ℂ)*(v:ℂ)^(-4/3:ℂ)*cubicThetaWindowHeight (4/3) v

lemma cubicThetaWindowFlux_hasDerivAt {v : ℝ} (hv : 0<v) :
    HasDerivAt cubicThetaWindowFlux
      ((v:ℂ)^(-7/3:ℂ)*cubicThetaWindowDefect (4/3) v) v := by
  have hH := cubicThetaWindowHeight_smooth (4/3:ℂ)
  have hHd := (contDiff_infty_iff_deriv.mp hH).2
  have h₁ := (cubicThetaHeightPower_hasDerivAt (-1/3) hv).mul
    (hHd.differentiable (by simp) v).hasDerivAt
  have h₂ := ((cubicThetaHeightPower_hasDerivAt (-4/3) hv).const_mul (2/3:ℂ)).mul
    (hH.differentiable (by simp) v).hasDerivAt
  have hn : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hp₁ : (v:ℂ)^(-1/3:ℂ)=(v:ℂ)^(-7/3:ℂ)*(v:ℂ)^2 := by
    rw [←Complex.cpow_ofNat,←Complex.cpow_add _ _ hn]
    congr 1
    ring
  have hp₂ : (v:ℂ)^(-4/3:ℂ)=(v:ℂ)^(-7/3:ℂ)*(v:ℂ) := by
    calc
      _ = (v:ℂ)^((-7/3:ℂ)+1) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ hn,Complex.cpow_one]
  convert h₁.sub h₂ using 1
  · rfl
  · norm_num only [show (-1/3:ℂ)-1= -4/3 by ring,
      show (-4/3:ℂ)-1= -7/3 by ring]
    simp only [neg_div] at hp₁ hp₂
    rw [hp₁,hp₂]
    unfold cubicThetaWindowDefect
    ring

lemma cubicThetaWindowHeight_high_deriv (s : ℂ) {v : ℝ} (hv : 4≤v) :
    deriv (cubicThetaWindowHeight s) v=0 := by
  have hc := (cubicThetaWindowHeight_smooth s).continuous_deriv
  have he : EqOn (deriv (cubicThetaWindowHeight s)) (fun _ => 0) (Ioi 4) := by
    intro x hx
    have hn : cubicThetaWindowHeight s =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [eventually_gt_nhds hx] with t ht
      exact cubicThetaWindowHeight_zero s (Or.inr ht.le)
    simpa only [deriv_const] using hn.deriv_eq
  exact he.closure (hc (by simp)) continuous_const (by simpa only [closure_Ioi,mem_Ici] using hv)

lemma cubicThetaWindowFlux_high {v : ℝ} (hv : 4≤v) :
    cubicThetaWindowFlux v=0 := by
  simp only [cubicThetaWindowFlux,cubicThetaWindowHeight_high_deriv _ hv,
    cubicThetaWindowHeight_zero _ (Or.inr hv),mul_zero,sub_self]

lemma cubicThetaCuspCutoff_deriv_endpoints :
    deriv cubicThetaCuspCutoff 1=0 ∧ deriv cubicThetaCuspCutoff 2=0 := by
  have hc := cubicThetaCuspCutoff_smooth.continuous_deriv (by simp)
  constructor
  · have he : EqOn (deriv cubicThetaCuspCutoff) (fun _ => 0) (Iio 1) :=
      fun _ hv => (cubicThetaCuspCutoff_derivatives_zero (Or.inl hv)).1
    exact he.closure hc continuous_const (by simp)
  · have he : EqOn (deriv cubicThetaCuspCutoff) (fun _ => 0) (Ioi 2) :=
      fun _ hv => (cubicThetaCuspCutoff_derivatives_zero (Or.inr hv)).1
    exact he.closure hc continuous_const (by simp)

lemma cubicThetaWindowHeight_two (s : ℂ) :
    cubicThetaWindowHeight s 2=(2:ℂ)^s := by
  simp only [cubicThetaWindowHeight,cubicThetaIncomingWindowCutoff,
    cubicThetaCuspCutoff_one (by norm_num : (2:ℝ)≤2),
    show (2:ℝ)/2=1 by norm_num,
    cubicThetaCuspCutoff_zero (by norm_num : (1:ℝ)≤1),sub_zero,one_mul,Complex.ofReal_ofNat]

lemma cubicThetaWindowHeight_two_deriv (s : ℂ) :
    deriv (cubicThetaWindowHeight s) 2=s*(2:ℂ)^(s-1) := by
  have hc : Differentiable ℝ cubicThetaCuspCutoff :=
    cubicThetaCuspCutoff_smooth.differentiable (by simp)
  have h₁ := (hc 2).hasDerivAt
  have h₂ := (hc ((2:ℝ)/2)).hasDerivAt.scomp (h:=fun t : ℝ => t/2) 2 ((hasDerivAt_id (2:ℝ)).div_const 2)
  norm_num only [id_eq,show (2:ℝ)/2=1 by norm_num] at h₂
  have hd := h₁.sub h₂
  rw [cubicThetaCuspCutoff_deriv_endpoints.1,cubicThetaCuspCutoff_deriv_endpoints.2] at hd
  have hp := hd.mul (cubicThetaHeightPower_hasDerivAt s (by norm_num : (0:ℝ)<2))
  change HasDerivAt (cubicThetaWindowHeight s) _ 2 at hp
  simpa only [Pi.sub_apply,Function.comp_apply,smul_zero,zero_mul,sub_zero,zero_add,cubicThetaIncomingWindowCutoff,
    cubicThetaCuspCutoff_one (by norm_num : (2:ℝ)≤2),
    show (2:ℝ)/2=1 by norm_num,
    cubicThetaCuspCutoff_zero (by norm_num : (1:ℝ)≤1),one_mul,Complex.ofReal_ofNat] using hp.deriv

lemma cubicThetaWindowFlux_two : cubicThetaWindowFlux 2=2/3 := by
  rw [cubicThetaWindowFlux,cubicThetaWindowHeight_two_deriv,cubicThetaWindowHeight_two]
  norm_num only [Complex.ofReal_ofNat]
  have h₁ : (2:ℂ)^(-1/3:ℂ)*(2:ℂ)^((4/3:ℂ)-1)=1 := by
    rw [←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    norm_num
  have h₂ : (2:ℂ)^(-4/3:ℂ)*(2:ℂ)^(4/3:ℂ)=1 := by
    rw [←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    norm_num
  calc
    _ = (4/3:ℂ)*((2:ℂ)^(-1/3:ℂ)*(2:ℂ)^((4/3:ℂ)-1)) -
        (2/3:ℂ)*((2:ℂ)^(-4/3:ℂ)*(2:ℂ)^(4/3:ℂ)) := by ring_nf
    _ = _ := by rw [h₁,h₂]; norm_num

end CubicFirstMoment

end

end OAI
