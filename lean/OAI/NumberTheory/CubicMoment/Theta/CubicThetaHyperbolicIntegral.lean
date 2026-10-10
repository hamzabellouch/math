import OAI.NumberTheory.CubicMoment.Theta.CubicThetaJacobian
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Group.Measure

namespace OAI

/-! Change of variables for the actual hyperbolic volume density v^-3.
This is the chart-independent integral used for the automorphic energy. -/
noncomputable section
open MeasureTheory Set
open scoped MatrixGroups
namespace CubicFirstMoment

local instance cubicThetaHyperbolicIntegral_volumeHaar :
    (volume : Measure (ℂ × ℝ)).IsAddHaarMeasure := by
  change ((volume : Measure ℂ).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

lemma cubicThetaMobius_injOn (g : SL(2,ℂ)) :
    Set.InjOn (cubicThetaMobius g) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp q hq he
  have h := congrArg (cubicThetaMobius g⁻¹) he
  rw [cubicThetaMobius_comp _ _ hp,cubicThetaMobius_comp _ _ hq] at h
  simpa only [inv_mul_cancel,cubicThetaMobius_one] using h

lemma cubicThetaHyperbolicIntegral_change (g : SL(2,ℂ)) {S : Set (ℂ × ℝ)}
    (hS : MeasurableSet S) (hpos : ∀ p∈S,0<p.2) (F : ℂ × ℝ → ℂ) :
    (∫ p in cubicThetaMobius g '' S, (p.2^3)⁻¹ • F p)=
      ∫ p in S, (p.2^3)⁻¹ • F (cubicThetaMobius g p) := by
  have hD : ∀ p∈S, HasFDerivWithinAt (cubicThetaMobius g)
      (fderiv ℝ (cubicThetaMobius g) p) S p := by
    intro p hp
    exact ((cubicThetaMobius_contDiffAt g (hpos p hp)).differentiableAt
      (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hS hD
    ((cubicThetaMobius_injOn g).mono hpos)]
  apply setIntegral_congr_fun hS
  intro p hp
  dsimp only
  rw [smul_smul]
  congr 1
  simpa only [div_eq_mul_inv,one_mul] using cubicThetaMobius_volume_density g (hpos p hp)

end CubicFirstMoment

end

end OAI
