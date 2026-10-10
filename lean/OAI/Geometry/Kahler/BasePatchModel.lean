import OAI.Geometry.Kahler.BaseModelParameters

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma densityHeight_power (k : ℕ) (p : Sphere) {ξ : Base} (hξ : 0 < ‖bracket ξ (p:Base)‖) :
    ‖bracket ξ (p:Base)‖^k = Real.exp (-densityHeight k p ξ) := by
  rw [densityHeight,neg_mul,neg_neg,Real.exp_nat_mul,Real.exp_log hξ]

lemma densityHeight_inv_sq {k : ℕ} (hk : 0 < k) (p : Sphere) {ξ : Base}
    (hξ : 0 < ‖bracket ξ (p:Base)‖) :
    (‖bracket ξ (p:Base)‖^2)⁻¹ = Real.exp (2*densityHeight k p ξ/k) := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have he : 2*densityHeight k p ξ/(k:ℝ) = -2*Real.log ‖bracket ξ (p:Base)‖ := by
    unfold densityHeight
    field_simp
  rw [he,show -2*Real.log ‖bracket ξ (p:Base)‖ = -(2*Real.log ‖bracket ξ (p:Base)‖) by ring,
    Real.exp_neg,show (2:ℝ) = (2:ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hξ]

def radialPatchModel (a ε ρ : ℝ) (k : ℕ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.exp (-2*y/k)*(Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2))-
    f y*(a*ρ*Real.exp (-y))/logFactor (a*ρ*Real.exp (-y)) ε

lemma radialMean_continuous (a ε ρ : ℝ) :
    Continuous (fun y : ℝ => Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2)) := by
  have hc : Continuous (fun y : ℝ => logFactor (a*ρ*Real.exp (-y)) ε) :=
    logFactor_continuous.comp (show Continuous (fun y : ℝ => (a*ρ*Real.exp (-y),ε)) from by fun_prop)
  exact (hc.log (fun y => (logFactor_pos _ _).ne')).sub continuous_const

lemma radialPatchModel_continuous (a ε ρ : ℝ) (k : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (radialPatchModel a ε ρ k f) := by
  have hr := radialMean_continuous a ε ρ
  have hq : Continuous (fun y : ℝ => a*ρ*Real.exp (-y)) := by fun_prop
  have hL : Continuous (fun y : ℝ => logFactor (a*ρ*Real.exp (-y)) ε) := logFactor_continuous.comp (hq.prodMk (continuous_const (y := ε)))
  exact ((show Continuous (fun y : ℝ => Real.exp (-2*y/k)) from by fun_prop).mul hr).sub
    ((hf.mul hq).div hL (fun y => (logFactor_pos _ _).ne'))

lemma ideal_patch_integral {a ε ρ : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ ρ) (hε : ε ≠ 0)
    (pr : RadialProfiles a) {k : ℕ} (hk : 0 < k) (p : Sphere) :
    (∫ ξ in peakPatch k pr.R p, regularizedLog a ε ((ρ:ℂ)*bracket (ξ:Base) (p:Base)^k)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma)=
      2/(k:ℝ)*(∫ y in 0..pr.R, radialPatchModel a ε ρ k pr.f y) := by
  let V : Sphere → ℝ := fun ξ => regularizedLog a ε ((ρ:ℂ)*bracket (ξ:Base) (p:Base)^k)*
    (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ)
  have hC := densityCorrection_smooth hk pr.cutoff_lt pr.smooth_f pr.smooth_b
    (show ContDiff ℝ ∞ (fun _ : Base => (1:ℝ)) from contDiff_const) pr.tail p
  have hV : Continuous V := ((regularizedLog_contDiff a hε).continuous.comp
    (continuous_const.mul (((bracket_analytic (p:Base)).continuous.comp continuous_subtype_val).pow k))).mul
      (continuous_const.add (hC.continuous.comp continuous_subtype_val))
  let H : ℝ → ℝ := fun y => Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2)-
    Real.exp (2*y/k)*pr.f y*(a*ρ*Real.exp (-y))/logFactor (a*ρ*Real.exp (-y)) ε
  have hq : Continuous (fun y : ℝ => a*ρ*Real.exp (-y)) := by fun_prop
  have hL : Continuous (fun y : ℝ => logFactor (a*ρ*Real.exp (-y)) ε) := logFactor_continuous.comp (hq.prodMk (continuous_const (y := ε)))
  have hH : Continuous H := (radialMean_continuous a ε ρ).sub
    ((((show Continuous (fun y : ℝ => Real.exp (2*y/k)) from by fun_prop).mul pr.smooth_f.continuous).mul hq).div hL
      (fun y => (logFactor_pos _ _).ne'))
  change (∫ ξ in peakPatch k pr.R p, V ξ ∂sigma)=_
  rw [sigma_phase_average_restrict hV (peakPatch_open k pr.R p).measurableSet
    (fun z ξ => phaseAction_patch k pr.R p ξ z)]
  calc
    _ = ∫ ξ in peakPatch k pr.R p, H (densityHeight k p ξ) ∂sigma := by
      apply setIntegral_congr_fun (peakPatch_open k pr.R p).measurableSet
      intro ξ hξ
      change (∫ z : Circle, regularizedLog a ε ((ρ:ℂ)*bracket (phaseAction z ξ : Base) (p:Base)^k)*
        (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p (phaseAction z ξ)) ∂circleMeasure)=_
      rw [ideal_patch_phase_mean ha hr hε hk pr.f pr.b hξ,
        densityHeight_power k p (peakPatch_norm_pos hξ),densityHeight_inv_sq hk p (peakPatch_norm_pos hξ)]
    _ = 2/(k:ℝ)*(∫ y in 0..pr.R, Real.exp (-2*y/k)*H y) := radial_patch_integral_exp hk pr.R_pos p hH
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro y hy
      dsimp only [H,radialPatchModel]
      have he : Real.exp (-2*y/k)*Real.exp (2*y/k)=1 := by
        rw [← Real.exp_add, show -2*y/(k:ℝ)+2*y/k=0 by ring, Real.exp_zero]
      calc
        _ = Real.exp (-2*y/k)*(Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2))-
          (Real.exp (-2*y/k)*Real.exp (2*y/k))*(pr.f y*(a*ρ*Real.exp (-y))/logFactor (a*ρ*Real.exp (-y)) ε) := by ring
        _ = _ := by rw [he,one_mul]

lemma peakPatch_measure_real {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R) (p : Sphere) :
    sigma.real (peakPatch k R p)=1-Real.exp (-2*R/k) := by
  have hh := radial_patch_integral hk hR p (continuous_const (y := (1:ℝ)))
  simpa using hh

lemma peakPatch_measure_le {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R) (p : Sphere) :
    sigma.real (peakPatch k R p) ≤ 2*R/k := by
  rw [peakPatch_measure_real hk hR]
  have hh := Real.one_sub_le_exp_neg (2*R/(k:ℝ))
  rw [← neg_div,← neg_mul] at hh
  linarith

end PinchedHartogs.BaseConstruction

end

end OAI
