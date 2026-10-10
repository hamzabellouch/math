import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.SpinParameterRegular
import OAI.Probability.SKBarriers.Scalar.PrefixAlgebra
import OAI.Probability.SKBarriers.Hierarchy.HierarchyParameterDerivative
import OAI.Probability.SKBarriers.Scalar.PathExponentialAverage

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem spinTerminal_parameterDerivative {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N))
    (c : Config N → ℝ) (a v : Fin d → ℝ) (z : ParameterSpace d) :
    fderiv ℝ (fun w : (Fin d → ℝ) × ParameterSpace d =>
      affineLogPartition c (spinExponent d w.1 I) w.2) (a,z) (v,0) =
      affineMoment c (spinExponent d a I) (fun s => spinExponent d v I s z) z := by
  rw [← parameterFDeriv_at_field ((spinTerminal_paramRegular d I c).1.differentiable (by norm_num))
    a v z]
  let L : Config N → (Fin d → ℝ) →L[ℝ] ℝ :=
    fun s => (spinCoefficientBilinear d I s).flip z
  have he : (fun a : Fin d → ℝ => affineLogPartition c (spinExponent d a I) z) =
      affineLogPartition c L := by
    funext a
    simp only [affineLogPartition,L,ContinuousLinearMap.flip_apply,
      spinCoefficientBilinear_apply]
  rw [he,fderiv_affineLogPartition_apply]
  simp only [affineMoment,affineGibbs,L,ContinuousLinearMap.flip_apply,spinCoefficientBilinear_apply]

theorem spinExponent_single {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N))
    (i : Fin d) (s : Config N) (z : ParameterSpace d) :
    spinExponent d (Pi.single i 1) I s z = spinMonomial s (I i)*coordinateProjection d i z := by
  classical
  simp [spinExponent,coordinateLinear_apply,Pi.single_apply]

theorem spinTerminal_parameterDerivative_single {N : ℕ} (d : ℕ)
    (I : Fin d → Finset (Fin N)) (a : Fin d → ℝ) (i : Fin d) (z : ParameterSpace d) :
    fderiv ℝ (fun w : (Fin d → ℝ) × ParameterSpace d =>
      affineLogPartition (fun _ => 0) (spinExponent d w.1 I) w.2) (a,z) (Pi.single i 1,0) =
      affineMoment (fun _ => 0) (spinExponent d a I) (fun s => spinMonomial s (I i)) z *
        coordinateProjection d i z := by
  rw [spinTerminal_parameterDerivative]
  simp only [spinExponent_single,affineMoment,Finset.sum_mul,mul_assoc]

theorem spinPressure_parameterDerivative_single {N : ℕ} (d : ℕ)
    (I : Fin d → Finset (Fin N)) (a : Fin d → ℝ) (m : Fin d → ℝ) (i : Fin d) :
    fderiv ℝ (fun a : Fin d → ℝ =>
      hierarchyPressure d m (affineLogPartition (fun _ => 0) (spinExponent d a I)) 0) a
      (Pi.single i 1) =
      ∫ sz, spinMonomial sz.1 (I i)*coordinateProjection d i sz.2
        ∂hierarchyGaussianLaw d m (spinExponent d a I) := by
  rw [parameterFDeriv_at_field ((spinPressure_paramRegular d I (fun _ => 0) m).1.differentiable (by norm_num)),
    hierarchyPressure_parameterDerivative d m _ (spinTerminal_paramRegular d I (fun _ => 0))]
  simp only [spinTerminal_parameterDerivative_single]
  rw [hierarchyAverage_eq_integral_exp d m _
    (affineLogPartition_boundedDerivs (fun _ => 0) (spinExponent d a I))]
  · exact (hierarchyGaussian_terminal_marginal d m (spinExponent d a I)
      (fun s => spinMonomial s (I i)) (coordinateProjection d i)
      (coordinateProjection d i).continuous (HasExpGrowth.linear _)).symm
  · exact (affineMoment_continuous _ _ _).mul (coordinateProjection d i).continuous
  · exact (HasExpGrowth.of_bounded (by norm_num : (0:ℝ) ≤ 1)
      (affineMoment_norm_le _ _ _ (fun s => by
        rw [Real.norm_eq_abs]
        exact (abs_le_one_iff_mul_self_le_one).mpr (by nlinarith [spinMonomial_sq s (I i)])))).mul (HasExpGrowth.linear _)
end SK.Analytic

end
end

end

end OAI
