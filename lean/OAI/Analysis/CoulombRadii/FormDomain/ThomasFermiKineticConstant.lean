import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PhaseRegion

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
namespace Coulomb
lemma fermiMeasure_center_lintegral (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ)
    (f : Space → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ yp, f yp.1 ∂phaseMeasure (fermiRadius ρ)) =
      ∫⁻ y : Space, f y * ENNReal.ofReal (ρ y/2) := by
  rw [phaseMeasure_lintegral (fermiRadius_measurable ρ hm) (fun yp : Space × Space => f yp.1) (hf.comp measurable_fst)]
  simp only [lintegral_const, Measure.restrict_apply_univ, fermiRadius_ball_mass ρ hρ]

lemma fermiMeasure_center_integral (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ)
    (f : Space → ℝ) (hf : Measurable f) (hfp : ∀ y, 0 ≤ f y) :
    (∫ yp, f yp.1 ∂phaseMeasure (fermiRadius ρ)) = (1/2:ℝ)*∫ y : Space, f y*ρ y := by
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun yp : Space × Space => f yp.1) (Filter.Eventually.of_forall (fun yp : Space × Space => hfp yp.1))
    (hf.comp measurable_fst).aestronglyMeasurable, fermiMeasure_center_lintegral ρ hρ hm _ hf.ennreal_ofReal]
  have he (y : Space) : ENNReal.ofReal (f y) * ENNReal.ofReal (ρ y/2) =
      ENNReal.ofReal ((1/2:ℝ)*(f y*ρ y)) := by
    rw [← ENNReal.ofReal_mul (hfp y)]
    congr 1
    ring
  simp only [he]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun y => mul_nonneg (by norm_num) (mul_nonneg (hfp y) (hρ y))))
    ((hf.mul hm).const_mul (1/2:ℝ)).aestronglyMeasurable, integral_const_mul]

noncomputable def thomasFermiKineticConstant : ℝ := (3/10:ℝ)*(3*Real.pi^2)^(2/3:ℝ)

lemma fermi_kinetic_coefficient :
    (2*Real.pi)^2 * (4*Real.pi/5) * (3/(8*Real.pi))^(5/3:ℝ) =
      thomasFermiKineticConstant := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hA : 0 < 3/(8*Real.pi) := by positivity
  have hpow : (3/(8*Real.pi))^(5/3:ℝ) =
      (3/(8*Real.pi)) * (3/(8*Real.pi))^(2/3:ℝ) := by
    rw [show (5/3:ℝ) = 1+2/3 by norm_num, Real.rpow_add hA, Real.rpow_one]
  have hphase : (2*Real.pi)^2 * (3/(8*Real.pi))^(2/3:ℝ) =
      (3*Real.pi^2)^(2/3:ℝ) := by
    have he : ((2*Real.pi)^3)^(2/3:ℝ) = (2*Real.pi)^2 := by
      rw [← Real.rpow_natCast_mul (by positivity)]
      norm_num
    rw [← he, ← Real.mul_rpow (by positivity) hA.le]
    congr 1
    field_simp
    ring
  rw [hpow]
  calc
    _ = (3/10:ℝ)*((2*Real.pi)^2 * (3/(8*Real.pi))^(2/3:ℝ)) := by field_simp; ring
    _ = thomasFermiKineticConstant := by rw [hphase]; rfl

lemma fermiMeasure_kinetic (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) :
    (2*Real.pi)^2 * (∫ yp, ‖yp.2‖^2 ∂phaseMeasure (fermiRadius ρ)) =
      thomasFermiKineticConstant * ∫ y : Space, ρ y^(5/3:ℝ) := by
  rw [phaseMeasure_real_momentum (fermiRadius_measurable ρ hm) (fermiRadius_nonneg ρ hρ)]
  simp only [fermiRadius_fifth ρ hρ, integral_const_mul]
  rw [← mul_assoc, ← mul_assoc, fermi_kinetic_coefficient]
end Coulomb

end

end OAI
