import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingWindow
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcingBoundary

namespace OAI

/-! The exact radial defect of the compact incoming window. Its difference
from the original forcing is a continuous weight supported in [2,4]. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

def cubicThetaWindowHeight (s : ℂ) (v : ℝ) : ℂ :=
  cubicThetaIncomingWindowCutoff v*(v:ℂ)^s

lemma cubicThetaWindowHeight_smooth (s : ℂ) : ContDiff ℝ ∞ (cubicThetaWindowHeight s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  by_cases hv : 0<v
  · exact cubicThetaIncomingWindowCutoff_smooth.contDiffAt.mul
      (cubicThetaHeightPower_analytic s hv).contDiffAt
  · have he : cubicThetaWindowHeight s =ᶠ[𝓝 v] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds (show v<1 by linarith)] with t ht
      simp only [cubicThetaWindowHeight,cubicThetaIncomingWindowCutoff_low ht.le,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma cubicThetaWindowHeight_zero {v : ℝ} (s : ℂ) (hv : v≤1 ∨ 4≤v) :
    cubicThetaWindowHeight s v=0 := by
  rcases hv with hv | hv
  · simp only [cubicThetaWindowHeight,cubicThetaIncomingWindowCutoff_low hv,zero_mul]
  · simp only [cubicThetaWindowHeight,cubicThetaIncomingWindowCutoff_high hv,zero_mul]

def cubicThetaWindowDefect (s : ℂ) (v : ℝ) : ℂ :=
  (v:ℂ)^2*deriv (deriv (cubicThetaWindowHeight s)) v-
    (v:ℂ)*deriv (cubicThetaWindowHeight s) v-s*(s-2)*cubicThetaWindowHeight s v

lemma cubicThetaWindowDefect_continuous (s : ℂ) : Continuous (cubicThetaWindowDefect s) := by
  have hd := (contDiff_infty_iff_deriv.mp (cubicThetaWindowHeight_smooth s)).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  exact ((Complex.continuous_ofReal.pow 2).mul hdd.continuous).sub
    (Complex.continuous_ofReal.mul hd.continuous) |>.sub
      (continuous_const.mul (cubicThetaWindowHeight_smooth s).continuous)

lemma cubicThetaWindowDefect_zero_open (s : ℂ) {v : ℝ} (hv : v<1 ∨ 4<v) :
    cubicThetaWindowDefect s v=0 := by
  have he : cubicThetaWindowHeight s =ᶠ[𝓝 v] (fun _ => 0) := by
    rcases hv with hv | hv
    · filter_upwards [eventually_lt_nhds hv] with t ht
      exact cubicThetaWindowHeight_zero s (Or.inl ht.le)
    · filter_upwards [eventually_gt_nhds hv] with t ht
      exact cubicThetaWindowHeight_zero s (Or.inr ht.le)
  have h₀ := he.eq_of_nhds
  have h₁ := he.deriv_eq
  have h₂ := he.deriv.deriv_eq
  simp only [deriv_const',deriv_const] at h₁ h₂
  simp only [cubicThetaWindowDefect,h₀,h₁,h₂,mul_zero,sub_zero]

lemma cubicThetaWindowDefect_low (s : ℂ) {v : ℝ} (hv : v<2) :
    cubicThetaWindowDefect s v=cubicThetaIncomingForcing s v := by
  by_cases hlow : v<1
  · rw [cubicThetaWindowDefect_zero_open s (Or.inl hlow),
      cubicThetaIncomingForcing_zero s (Or.inl hlow)]
  have he : cubicThetaWindowHeight s =ᶠ[𝓝 v]
      (fun t => cubicThetaCuspCutoff t*(t:ℂ)^s) := by
    filter_upwards [eventually_lt_nhds hv] with t ht
    simp only [cubicThetaWindowHeight,cubicThetaIncomingWindowCutoff,
      cubicThetaCuspCutoff_zero (by linarith : t/2≤1),sub_zero]
  have h₀ := he.eq_of_nhds
  have h₁ := he.deriv_eq
  have h₂ := he.deriv.deriv_eq
  have h := cubicThetaCutoffIncoming_equation s 0 0 (show 0<v by linarith)
  simp only [cubicThetaHyperbolicOperator,deriv_const',deriv_const,zero_add] at h
  unfold cubicThetaWindowDefect
  rw [h₀,h₁,h₂,h]
  ring

lemma cubicThetaIncomingForcing_continuous (s : ℂ) : Continuous (cubicThetaIncomingForcing s) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  by_cases hv : 0<v
  · exact (cubicThetaIncomingForcing_contDiffAt s hv).continuousAt
  · have he : cubicThetaIncomingForcing s =ᶠ[𝓝 v] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds (show v<1 by linarith)] with t ht
      exact cubicThetaIncomingForcing_zero s (Or.inl ht)
    exact continuousAt_const.congr_of_eventuallyEq he

def cubicThetaHighWindowForcing (s : ℂ) (v : ℝ) : ℂ :=
  cubicThetaIncomingForcing s v-cubicThetaWindowDefect s v

lemma cubicThetaHighWindowForcing_continuous (s : ℂ) :
    Continuous (cubicThetaHighWindowForcing s) :=
  (cubicThetaIncomingForcing_continuous s).sub (cubicThetaWindowDefect_continuous s)

lemma cubicThetaHighWindowForcing_low (s : ℂ) {v : ℝ} (hv : v≤2) :
    cubicThetaHighWindowForcing s v=0 := by
  have hz : EqOn (cubicThetaHighWindowForcing s) (fun _ => 0) (Iio (2:ℝ)) := by
    intro t ht
    rw [cubicThetaHighWindowForcing,cubicThetaWindowDefect_low s ht,sub_self]
  exact hz.closure (cubicThetaHighWindowForcing_continuous s) continuous_const
    (by simpa only [closure_Iio,mem_Iic] using hv)

lemma cubicThetaHighWindowForcing_high (s : ℂ) {v : ℝ} (hv : 4≤v) :
    cubicThetaHighWindowForcing s v=0 := by
  have hz : EqOn (cubicThetaHighWindowForcing s) (fun _ => 0) (Ioi (4:ℝ)) := by
    intro t ht
    change 4<t at ht
    rw [cubicThetaHighWindowForcing,cubicThetaWindowDefect_zero_open s (Or.inr ht),
      cubicThetaIncomingForcing_zero s (Or.inr (by linarith : 2<t)),sub_zero]
  exact hz.closure (cubicThetaHighWindowForcing_continuous s) continuous_const
    (by simpa only [closure_Ioi,mem_Ici] using hv)

def cubicThetaHighWindowWeight (s : ℂ) : C_c(ℝ,ℂ) where
  toFun := cubicThetaHighWindowForcing s
  continuous_toFun := cubicThetaHighWindowForcing_continuous s
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact (K:=Icc (2:ℝ) 4) isCompact_Icc
    intro v hv
    constructor
    · by_contra hn
      exact hv (cubicThetaHighWindowForcing_low s (le_of_not_ge hn))
    · by_contra hn
      exact hv (cubicThetaHighWindowForcing_high s (le_of_not_ge hn))

lemma cubicThetaWindowHeight_equation (s : ℂ) (x y v : ℝ) :
    cubicThetaHyperbolicOperator (fun _ _ t => cubicThetaWindowHeight s t) x y v=
      s*(s-2)*cubicThetaWindowHeight s v+cubicThetaIncomingForcing s v-
        cubicThetaHighWindowForcing s v := by
  simp only [cubicThetaHyperbolicOperator,deriv_const',deriv_const,zero_add,
    cubicThetaHighWindowForcing,cubicThetaWindowDefect]
  ring

end CubicFirstMoment

end

end OAI
