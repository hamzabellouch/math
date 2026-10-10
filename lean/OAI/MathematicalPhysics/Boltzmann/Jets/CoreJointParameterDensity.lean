import OAI.MathematicalPhysics.Boltzmann.Jets.CoreDensityTranslation
import OAI.MathematicalPhysics.Boltzmann.Branching.RescaledParameterSlab

namespace OAI

/-! # Joint measurability of the physical six-parameter collision density -/

noncomputable section

open MeasureTheory
open scoped Matrix ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetCoreDensity

namespace BoltzmannNonuniqueness.RedundantPlane

theorem joint_point_measurable : Measurable (fun p : (Velocity × Velocity) × V =>
    p.1.1+crossVelocity p.1.1 p.1.2 p.2) := by
  apply measurable_fst.fst.add
  apply (MeasurableEquiv.toLp 2 V).measurable.comp
  apply Measurable.of_eval
  intro i
  fin_cases i <;> simp only [normalVector,cross_apply] <;> fun_prop

theorem joint_normalCoefficient_measurable :
    Measurable (fun p : (Velocity × Velocity) × V => normalCoefficient p.1.1 p.1.2 p.2) := by
  unfold normalCoefficient normalVector normSq
  simp only [Matrix.vec3_dotProduct]
  fun_prop

end BoltzmannNonuniqueness.RedundantPlane

namespace BoltzmannNonuniqueness.JetCoreSheet

abbrev ParameterArguments := (ℝ × JetPrototype.Space) × (Velocity × (FiveGainMap.V × FiveGainMap.V))

attribute [local irreducible] thermalPoint parameterPoint parameterDensity
  thermalWeight RedundantPlane.normalCoefficient RedundantPlane.normalDensity

private theorem arguments_measurable : Measurable (fun p : ParameterArguments =>
    ((p.1.1,p.1.2,p.2.2.1) : ThermalArguments)) := by fun_prop

theorem clamped_parameterPoint_measurable {α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (d : ℝ) (color : Bool) :
    Measurable (fun p : ParameterArguments => parameterPoint α γ s d (max 0 p.1.1) color
      p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  have hc : Measurable (fun p : ParameterArguments =>
      thermalPoint α γ s d (max 0 p.1.1) color p.1.2 p.2.2.1) :=
    (clamped_thermalPoint_measurable hα hγ hs d color).comp arguments_measurable
  unfold parameterPoint
  exact RedundantPlane.joint_point_measurable.comp
    ((measurable_snd.fst.prodMk hc).prodMk measurable_snd.snd.snd)

private theorem clamped_normalDensity_measurable {α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (d : ℝ) (color : Bool) :
    Measurable (fun p : ParameterArguments => RedundantPlane.normalDensity
      (RedundantPlane.normalCoefficient p.2.1
        (thermalPoint α γ s d (max 0 p.1.1) color p.1.2 p.2.2.1) p.2.2.2)) := by
  have hc : Measurable (fun p : ParameterArguments =>
      thermalPoint α γ s d (max 0 p.1.1) color p.1.2 p.2.2.1) :=
    (clamped_thermalPoint_measurable hα hγ hs d color).comp arguments_measurable
  have harg : Measurable (fun p : ParameterArguments =>
      ((p.2.1,thermalPoint α γ s d (max 0 p.1.1) color p.1.2 p.2.2.1),p.2.2.2)) :=
    (measurable_snd.fst.prodMk hc).prodMk measurable_snd.snd.snd
  apply RedundantPlane.measurable_normalDensity.comp
  exact RedundantPlane.joint_normalCoefficient_measurable.comp harg

private theorem clamped_ratio_measurable {α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (d q : ℝ) (color : Bool) :
    Measurable (fun p : ParameterArguments => ENNReal.ofReal
      (H q (parameterPoint α γ s d (max 0 p.1.1) color p.1.2 p.2.1 p.2.2.1 p.2.2.2)/H q p.2.1)) := by
  have hp := clamped_parameterPoint_measurable hα hγ hs d color
  have hnum : Measurable (fun p : ParameterArguments =>
      H q (parameterPoint α γ s d (max 0 p.1.1) color p.1.2 p.2.1 p.2.2.1 p.2.2.2)) :=
    (ChartKernel.measurable_H q).comp hp
  have hden : Measurable (fun p : ParameterArguments => H q p.2.1) :=
    (ChartKernel.measurable_H q).comp measurable_snd.fst
  exact (hnum.div hden).ennreal_ofReal

theorem clamped_parameterDensity_measurable {α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (η K d q : ℝ) (color : Bool) :
    Measurable (fun p : ParameterArguments => parameterDensity η K α γ s d (max 0 p.1.1) q color
      p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  have hw : Measurable (fun p : ParameterArguments =>
      thermalWeight η K α γ s d (max 0 p.1.1) color p.1.2 p.2.2.1) :=
    (clamped_thermalWeight_measurable hα hγ hs η K d color).comp arguments_measurable
  have hn := clamped_normalDensity_measurable hα hγ hs d color
  have hr := clamped_ratio_measurable hα hγ hs d q color
  unfold parameterDensity
  exact ((measurable_const.mul hw.ennreal_ofReal).mul hn).mul hr

theorem clamped_rescaledParameterDensity_measurable {r α γ μ : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (η K d q : ℝ) (color : Bool) :
    Measurable (fun p : ParameterArguments =>
      rescaledParameterDensity r η K α γ μ d (max 0 p.1.1) q color
        p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  have h := (clamped_parameterDensity_measurable hα hγ (mul_pos hr hμ) η K d q color).comp
    (show Measurable (fun p : ParameterArguments => ((r*p.1.1,r • p.1.2),p.2)) by fun_prop)
  have hm (t : ℝ) : max 0 (r*t) = r*max 0 t := by
    rw [mul_max_of_nonneg _ _ hr.le,mul_zero]
  unfold rescaledParameterDensity
  apply measurable_const.mul
  simpa only [Function.comp_def,hm] using h

end BoltzmannNonuniqueness.JetCoreSheet

end

end OAI
