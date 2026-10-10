import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAutomorphicSections
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! Compact chart localization of actual automorphic sections. The factor
v^(-3/2) is the exact square root of the hyperbolic volume density. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaLocalizedSection (ψ : ℂ × ℝ → ℂ) (F : CubicThetaSection) (y : ℂ × ℝ) : ℂ :=
  ψ y*((y.2^(-3/2:ℝ):ℝ):ℂ)*F.val (cubicThetaPointInclusion.symm y)

lemma cubicThetaLocalizedSection_compact {ψ : ℂ × ℝ → ℂ} (hψ : HasCompactSupport ψ)
    (F : CubicThetaSection) : HasCompactSupport (cubicThetaLocalizedSection ψ F) :=
  (hψ.mul_right).mul_right

lemma cubicThetaLocalizedSection_continuous {ψ : ℂ × ℝ → ℂ} (hψ : Continuous ψ)
    (hpos : tsupport ψ ⊆ {y : ℂ × ℝ | 0<y.2}) (F : CubicThetaSection) :
    Continuous (cubicThetaLocalizedSection ψ F) := by
  have hweight : ContinuousOn (fun y : ℂ × ℝ => ((y.2^(-3/2:ℝ):ℝ):ℂ)) {y | 0<y.2} :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuous_snd.continuousOn.rpow_const (fun y hy => Or.inl hy.ne'))
  have hinc : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  have hloc : ContinuousOn (cubicThetaLocalizedSection ψ F) {y : ℂ × ℝ | 0<y.2} :=
    (hψ.continuousOn.mul hweight).mul (F.val.continuous.comp_continuousOn hinc)
  apply hloc.continuous_of_tsupport_subset (isOpen_lt continuous_const continuous_snd)
  exact (tsupport_mul_subset_left.trans tsupport_mul_subset_left).trans hpos

lemma cubicThetaLocalizedSection_memLp {ψ : ℂ × ℝ → ℂ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ {y : ℂ × ℝ | 0<y.2})
    (F : CubicThetaSection) :
    MemLp (cubicThetaLocalizedSection ψ F) 2 (volume : Measure (ℂ × ℝ)) :=
  (cubicThetaLocalizedSection_continuous hψ hpos F).memLp_of_hasCompactSupport
    (cubicThetaLocalizedSection_compact hc F)

lemma cubicThetaLocalizedSection_norm_sq (ψ : ℂ × ℝ → ℂ) (F : CubicThetaSection)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    ‖cubicThetaLocalizedSection ψ F y‖^2=
      ‖ψ y‖^2*‖F.val (cubicThetaPointInclusion.symm y)‖^2/y.2^3 := by
  have hw : (y.2^(-3/2:ℝ))^2=(y.2^3)⁻¹ := by
    rw [← Real.rpow_mul_natCast hy.le]
    norm_num
  unfold cubicThetaLocalizedSection
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hy.le _),mul_pow,mul_pow,hw]
  ring

end CubicFirstMoment

end

end OAI
