import Mathlib
import OAI.Analysis.Conductivity.Variational.WeakWeyl

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace
open scoped Convolution

lemma WeaklyHarmonicOn.congr_ae {f g : WeylSpace → ℝ} {U : Set WeylSpace}
    (he : f =ᵐ[volume] g) (hf : WeaklyHarmonicOn f U) : WeaklyHarmonicOn g U := by
  intro ψ hψ hc hs
  rw [←hf ψ hψ hc hs]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

lemma laplacian_zero_off_support {ψ : WeylSpace → ℝ} {x : WeylSpace}
    (hx : x∉tsupport ψ) : Δ ψ x=0 := by
  have he : ψ =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
    filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [(laplacian_congr_nhds he).eq_of_nhds]
  simp

lemma WeaklyHarmonicOn.congr_restrict {f g : WeylSpace → ℝ} {U : Set WeylSpace}
    (hU : MeasurableSet U) (he : f =ᵐ[volume.restrict U] g)
    (hf : WeaklyHarmonicOn f U) : WeaklyHarmonicOn g U := by
  intro ψ hψ hc hs
  rw [←hf ψ hψ hc hs]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hU).mp he] with x hx
  by_cases h : x∈U
  · rw [hx h]
  · have he : Δ ψ x=0 := laplacian_zero_off_support (fun hy => h (hs hy))
    simp [he]

lemma weaklyHarmonic_smooth_mean {f : WeylSpace → ℝ} {a : WeylSpace} {R : ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hc : HasCompactSupport f)
    (hw : WeaklyHarmonicOn f (Metric.ball a R)) : RadialMeanOn f a (R/4) := by
  have hm : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport hc
  let fl : WholeL2 := hm.toLp f
  have hw' : WeaklyHarmonicOn fl (Metric.ball a R) := .congr_ae hm.coeFn_toLp.symm hw
  intro s hs x hx
  have hball : Metric.closedBall x (4*s)⊆Metric.ball a R := by
    intro y hy
    have hy' : dist y x ≤ 4*s := hy
    have hd := dist_triangle y x a
    change dist y a<R
    have hx' : 0≤dist x a := dist_nonneg
    linarith
  obtain ⟨hsm,he⟩ := weakWeyl_local hw' (by positivity : 0<4*s) hball
  have hcvg : radialMollify fl s=radialMollify f s :=
    convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) hm.coeFn_toLp Filter.EventuallyEq.rfl
  have he' : f =ᵐ[volume.restrict (Metric.ball x s)] radialMollify f s := by
    have hh : f =ᵐ[volume.restrict (Metric.ball x (4*s/4))] fl :=
      ae_restrict_of_ae hm.coeFn_toLp.symm
    have h := hh.trans he
    have hs4 : 4*s/4=s := by ring
    simpa only [hs4,hcvg] using h
  have hp := Measure.eqOn_open_of_ae_eq he' Metric.isOpen_ball hf.continuous.continuousOn
    (radialMollify_smooth hf.continuous.locallyIntegrable hs).continuous.continuousOn (Metric.mem_ball_self hs)
  rw [hp,radialMollify_eq_average hs,radialProbability_integral hs]
  rfl

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma radialEta_as_scale {s : ℝ} (_ : 0<s) :
    radialEta radialProfile s = fun x => s⁻¹^3 * radialEta radialProfile 1 (s⁻¹ • x) := by
  ext x
  simp [radialEta,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_eq_mul_inv,mul_comm]

lemma radialEta_fderiv_scale {s : ℝ} (hs : 0<s) (x : WeylSpace) :
    fderiv ℝ (radialEta radialProfile s) x =
      s⁻¹^4 • fderiv ℝ (radialEta radialProfile 1) (s⁻¹ • x) := by
  have hd := (((radialEta_smooth 1).differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul s⁻¹)).const_smul (s⁻¹^3)
  rw [radialEta_as_scale hs]
  refine hd.fderiv.trans ?_
  ext v
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_smul]
  congr 1

def radialGradientMass : ℝ := ∫ x, ‖fderiv ℝ (radialEta radialProfile 1) x‖

lemma radialGradientMass_nonneg : 0≤radialGradientMass := integral_nonneg (fun _ => norm_nonneg _)

lemma radialEta_gradient_integral {s : ℝ} (hs : 0<s) :
    (∫ x, ‖fderiv ℝ (radialEta radialProfile s) x‖)=radialGradientMass/s := by
  simp_rw [radialEta_fderiv_scale hs,norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ s⁻¹^4)]
  rw [integral_const_mul,Measure.integral_comp_smul volume (fun x : WeylSpace => ‖fderiv ℝ (radialEta radialProfile 1) x‖)]
  simp only [WeylSpace,finrank_euclideanSpace,Fintype.card_fin,inv_pow,inv_inv,smul_eq_mul]
  rw [abs_of_pos (pow_pos hs 3)]
  change (s^4)⁻¹ * (s^3*radialGradientMass)=radialGradientMass/s
  field_simp [hs.ne']

end ScalarConductivity

end

end OAI
