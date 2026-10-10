import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.SpinMonomials
import OAI.Probability.SKBarriers.Calculus.ParameterBilinear
import OAI.Probability.SKBarriers.Calculus.ParameterFiniteLog
import OAI.Probability.SKBarriers.Calculus.ParameterRecursion
import OAI.Probability.SKBarriers.Hierarchy.CascadeBlockLaw

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def spinCoefficientBilinear {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N)) (s : Config N) :
    (Fin d → ℝ) →L[ℝ] ParameterSpace d →L[ℝ] ℝ :=
  ∑ i : Fin d, (ContinuousLinearMap.proj i).smulRight
    (spinMonomial s (I i) • coordinateProjection d i)

theorem spinCoefficientBilinear_apply {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N))
    (s : Config N) (a : Fin d → ℝ) : spinCoefficientBilinear d I s a = spinExponent d a I s := by
  simp only [spinCoefficientBilinear,sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply,spinExponent,coordinateLinear,smul_smul]

theorem spinExponent_paramRegular {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N)) (s : Config N) :
    ParamRegular (fun z : (Fin d → ℝ) × ParameterSpace d => spinExponent d z.1 I s z.2) := by
  simpa only [spinCoefficientBilinear_apply] using paramRegular_bilinear (spinCoefficientBilinear d I s)

theorem spinTerminal_paramRegular {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N)) (c : Config N → ℝ) :
    ParamRegular (fun z : (Fin d → ℝ) × ParameterSpace d =>
      affineLogPartition c (spinExponent d z.1 I) z.2) := by
  exact paramRegular_log_finite_exp (fun s z => c s+spinExponent d z.1 I s z.2)
    (fun s => (paramRegular_const (c s)).add (spinExponent_paramRegular d I s))

section ParameterHierarchy
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem hierarchyPressure_paramRegular (n : ℕ) (m : Fin n → ℝ)
    (f : P × ParameterSpace n → ℝ) (hf : ParamRegular f) :
    ParamRegular (fun z : P × ℝ => hierarchyPressure n m (fun w => f (z.1,w)) z.2) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact ih (fun i => m i.castSucc)
      (gaussianStep (m (Fin.last n)) (fun z : (P × ParameterSpace n) × ℝ =>
        f (z.1.1,(z.1.2,z.2)))) (hf.gaussianStep (m (Fin.last n)))

end ParameterHierarchy

theorem spinPressure_paramRegular {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N))
    (c : Config N → ℝ) (m : Fin d → ℝ) :
    ParamRegular (fun z : (Fin d → ℝ) × ℝ =>
      hierarchyPressure d m (affineLogPartition c (spinExponent d z.1 I)) z.2) :=
  hierarchyPressure_paramRegular d m _ (spinTerminal_paramRegular d I c)
end SK.Analytic

end
end

end

end OAI
