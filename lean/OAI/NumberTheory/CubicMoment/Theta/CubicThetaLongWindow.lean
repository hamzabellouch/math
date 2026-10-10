import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialEulerScaling
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialWeightScaling
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHighWindowSmooth

namespace OAI

/-! A compact incoming window between heights one and H. Its defect is
exactly the difference of the original and dilated annular forcing. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

def cubicThetaCutoffHeight (s : ℂ) (v : ℝ) : ℂ :=
  cubicThetaCuspCutoff v*(v:ℂ)^s

lemma cubicThetaCutoffHeight_smooth (s : ℂ) :
    ContDiff ℝ ∞ (cubicThetaCutoffHeight s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  by_cases hv : 0<v
  · exact cubicThetaCuspCutoff_smooth.contDiffAt.mul
      (cubicThetaHeightPower_analytic s hv).contDiffAt
  · have he : cubicThetaCutoffHeight s =ᶠ[𝓝 v] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds (show v<1 by linarith)] with t ht
      simp only [cubicThetaCutoffHeight,cubicThetaCuspCutoff_zero ht.le,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma cubicThetaCutoffHeight_equation (s : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaRadialEuler (cubicThetaCutoffHeight s) v=
      s*(s-2)*cubicThetaCutoffHeight s v+cubicThetaIncomingForcing s v := by
  have h := cubicThetaCutoffIncoming_equation s 0 0 hv
  change (v:ℂ)^2*deriv (deriv (fun t => cubicThetaCuspCutoff t*(t:ℂ)^s)) v-
    (v:ℂ)*deriv (fun t => cubicThetaCuspCutoff t*(t:ℂ)^s) v=_
  dsimp only [cubicThetaCutoffHeight]
  simpa only [cubicThetaHyperbolicOperator,deriv_const',deriv_const,zero_add] using h

def cubicThetaLongWindowHeight (H : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  cubicThetaCutoffHeight s v-(H:ℂ)^s*cubicThetaCutoffHeight s (v/H)

lemma cubicThetaLongWindowHeight_smooth (H : ℝ) (s : ℂ) :
    ContDiff ℝ ∞ (cubicThetaLongWindowHeight H s) :=
  (cubicThetaCutoffHeight_smooth s).sub (contDiff_const.mul
    ((cubicThetaCutoffHeight_smooth s).comp (contDiff_id.div_const H)))

lemma cubicThetaLongWindowHeight_low {H : ℝ} (hH : 1≤H) (s : ℂ)
    {v : ℝ} (hv : v≤1) : cubicThetaLongWindowHeight H s v=0 := by
  have hvH : v/H≤1 := (div_le_iff₀ (by linarith : 0<H)).mpr (by linarith)
  simp only [cubicThetaLongWindowHeight,cubicThetaCutoffHeight,
    cubicThetaCuspCutoff_zero hv,cubicThetaCuspCutoff_zero hvH,zero_mul,mul_zero,sub_self]

lemma cubicThetaLongWindowHeight_high {H : ℝ} (hH : 1≤H) (s : ℂ)
    {v : ℝ} (hv : 2*H≤v) : cubicThetaLongWindowHeight H s v=0 := by
  have hH0 : 0<H := by linarith
  have hv2 : 2≤v := by linarith
  have hvH : 2≤v/H := (le_div_iff₀ hH0).mpr hv
  have he : (H:ℂ)^s*((v/H:ℝ):ℂ)^s=(v:ℂ)^s := by
    rw [←Complex.mul_cpow_ofReal_nonneg hH0.le (div_nonneg (by linarith) hH0.le),
      ←Complex.ofReal_mul]
    congr 1
    field_simp
  simp only [cubicThetaLongWindowHeight,cubicThetaCutoffHeight,
    cubicThetaCuspCutoff_one hv2,cubicThetaCuspCutoff_one hvH,one_mul,he,sub_self]

def cubicThetaLongWindowWeight (H : ℝ) (hH : 1≤H) (s : ℂ) : C_c(ℝ,ℂ) where
  toFun := cubicThetaLongWindowHeight H s
  continuous_toFun := (cubicThetaLongWindowHeight_smooth H s).continuous
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact (K:=Icc (1:ℝ) (2*H)) isCompact_Icc
    intro v hv
    constructor
    · by_contra hn
      exact hv (cubicThetaLongWindowHeight_low hH s (le_of_not_ge hn))
    · by_contra hn
      exact hv (cubicThetaLongWindowHeight_high hH s (le_of_not_ge hn))

def cubicThetaIncomingForcingWeight (s : ℂ) : C_c(ℝ,ℂ) where
  toFun := cubicThetaIncomingForcing s
  continuous_toFun := cubicThetaIncomingForcing_continuous s
  hasCompactSupport' := cubicThetaIncomingForcing_compact s

def cubicThetaLongForcingWeight (H : ℝ) (hH : 0<H) (s : ℂ) : C_c(ℝ,ℂ) :=
  (H:ℂ)^s • cubicThetaRadialWeightScale H⁻¹ (inv_pos.mpr hH) (cubicThetaIncomingForcingWeight s)

lemma cubicThetaLongForcingWeight_apply (H : ℝ) (hH : 0<H) (s : ℂ) (v : ℝ) :
    cubicThetaLongForcingWeight H hH s v=(H:ℂ)^s*cubicThetaIncomingForcing s (v/H) := by
  change (H:ℂ)^s*cubicThetaIncomingForcing s (H⁻¹*v)=_
  rw [div_eq_mul_inv,mul_comm H⁻¹ v]

lemma cubicThetaLongForcingWeight_low {H : ℝ} (hH : 0<H) (s : ℂ)
    {v : ℝ} (hv : v≤H) : cubicThetaLongForcingWeight H hH s v=0 := by
  rw [cubicThetaLongForcingWeight_apply,cubicThetaIncomingForcing_zero_closed s
    (Or.inl ((div_le_one hH).mpr hv)),mul_zero]

lemma cubicThetaLongWindowHeight_equation {H : ℝ} (hH : 1≤H) (s : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaRadialEuler (cubicThetaLongWindowHeight H s) v=
      s*(s-2)*cubicThetaLongWindowHeight H s v+cubicThetaIncomingForcing s v-
        cubicThetaLongForcingWeight H (by linarith) s v := by
  have hH0 : 0<H := by linarith
  change cubicThetaRadialEuler
    (fun t => cubicThetaCutoffHeight s t-(H:ℂ)^s*cubicThetaCutoffHeight s (t/H)) v=_
  have hd : ContDiff ℝ ∞ (fun t => (H:ℂ)^s*cubicThetaCutoffHeight s (t/H)) :=
    contDiff_const.mul ((cubicThetaCutoffHeight_smooth s).comp (contDiff_id.div_const H))
  rw [cubicThetaRadialEuler_sub (cubicThetaCutoffHeight_smooth s) hd,
    cubicThetaRadialEuler_const_mul,cubicThetaRadialEuler_scale hH0
      ((cubicThetaCutoffHeight_smooth s).contDiffAt.of_le (by norm_num)),
    cubicThetaCutoffHeight_equation s hv,cubicThetaCutoffHeight_equation s (div_pos hv hH0),
    cubicThetaLongForcingWeight_apply]
  dsimp only [cubicThetaLongWindowHeight]
  ring

end CubicFirstMoment

end

end OAI
