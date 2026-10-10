import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcingBoundary
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace OAI

/-! The forcing profile is an entire function with values in the
supremum-norm space on the fixed radial annulus. -/
noncomputable section
namespace CubicFirstMoment

abbrev CubicThetaForcingBand := ↥(Set.Icc (1:ℝ) 2)

def cubicThetaForcingLog : C(CubicThetaForcingBand,ℂ) :=
  ⟨fun v => (Real.log v.val:ℂ), Complex.continuous_ofReal.comp
    (continuous_subtype_val.log (fun v => ne_of_gt (lt_of_lt_of_le zero_lt_one v.property.1)))⟩

def cubicThetaForcingA : C(CubicThetaForcingBand,ℂ) :=
  ⟨fun v => (v.val:ℂ)^2*deriv (deriv cubicThetaCuspCutoff) v.val-
    (v.val:ℂ)*deriv cubicThetaCuspCutoff v.val,by
    have hd := (contDiff_infty_iff_deriv.mp cubicThetaCuspCutoff_smooth).2
    have hdd := (contDiff_infty_iff_deriv.mp hd).2
    have hc := Complex.continuous_ofReal.comp (continuous_subtype_val (p:=fun v : ℝ => v∈Set.Icc 1 2))
    exact ((hc.pow 2).mul (hdd.continuous.comp continuous_subtype_val)).sub
      (hc.mul (hd.continuous.comp continuous_subtype_val))⟩

def cubicThetaForcingB : C(CubicThetaForcingBand,ℂ) :=
  ⟨fun v => 2*(v.val:ℂ)*deriv cubicThetaCuspCutoff v.val,by
    have hd := (contDiff_infty_iff_deriv.mp cubicThetaCuspCutoff_smooth).2
    exact (continuous_const.mul (Complex.continuous_ofReal.comp continuous_subtype_val)).mul
      (hd.continuous.comp continuous_subtype_val)⟩

def cubicThetaForcingProfile (s : ℂ) : C(CubicThetaForcingBand,ℂ) :=
  cubicThetaForcingA*NormedSpace.exp (s • cubicThetaForcingLog)+
    s • (cubicThetaForcingB*NormedSpace.exp (s • cubicThetaForcingLog))

theorem cubicThetaForcingProfile_analytic (s : ℂ) :
    AnalyticAt ℂ cubicThetaForcingProfile s := by
  have hl : AnalyticAt ℂ (fun z : ℂ => z • cubicThetaForcingLog) s :=
    analyticAt_id.smul analyticAt_const
  have he := (NormedSpace.exp_analytic (𝕂:=ℂ) (s • cubicThetaForcingLog)).comp
    (f:=fun z : ℂ => z • cubicThetaForcingLog) (x:=s) hl
  exact (analyticAt_const.mul he).add (analyticAt_id.smul (analyticAt_const.mul he))

lemma cubicThetaForcingProfile_apply (s : ℂ) (v : CubicThetaForcingBand) :
    cubicThetaForcingProfile s v=cubicThetaIncomingForcing s v.val := by
  have hv : 0<v.val := lt_of_lt_of_le zero_lt_one v.property.1
  have he := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ v)
    (ContinuousMap.evalCLM (R:=ℂ) v).continuous (s • cubicThetaForcingLog)
  change (NormedSpace.exp (s • cubicThetaForcingLog)) v=
    NormedSpace.exp (s*(Real.log v.val:ℂ)) at he
  rw [← Complex.exp_eq_exp_ℂ] at he
  have hp : (NormedSpace.exp (s • cubicThetaForcingLog)) v=(v.val:ℂ)^s := by
    rw [he,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hv.ne'),
      ← Complex.ofReal_log hv.le,mul_comm]
  change cubicThetaForcingA v*(NormedSpace.exp (s • cubicThetaForcingLog)) v+
    s*(cubicThetaForcingB v*(NormedSpace.exp (s • cubicThetaForcingLog)) v)=_
  rw [hp]
  unfold cubicThetaForcingA cubicThetaForcingB cubicThetaIncomingForcing
  simp only [ContinuousMap.coe_mk]
  rw [Complex.cpow_sub s 1 (Complex.ofReal_ne_zero.mpr hv.ne'),Complex.cpow_one]
  field_simp [Complex.ofReal_ne_zero.mpr hv.ne']

end CubicFirstMoment

end

end OAI
