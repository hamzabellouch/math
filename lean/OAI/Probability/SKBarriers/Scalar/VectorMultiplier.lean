import Mathlib
import OAI.Probability.SKBarriers.Scalar.EmbeddedSites
import OAI.Probability.SKBarriers.Scalar.VectorAverage
import OAI.Probability.SKBarriers.Scalar.MultiplierTaylor

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorStep_translate (m : ℝ) (v c : E) (f : E → ℝ) (x : E) :
    vectorStep m v (fun y => f (c+y)) x=vectorStep m v f (c+x) := by
  simp only [vectorStep,gaussianStep,positiveGaussianLogStep,add_assoc]

theorem vectorHierarchy_translate (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E)
    (f : E → ℝ) (c x : E) :
    vectorHierarchy n m v (fun y => f (c+y)) x=vectorHierarchy n m v f (c+x) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [vectorHierarchy]
    rw [funext (vectorStep_translate _ _ c f)]
    exact ih _ _ _
end Vector

section Site
variable {S : Type} [Fintype S] [Nonempty S]

def siteMultiplierExponent (n : ℕ) (V : Fin n → S → ℝ) (O : S → ℝ) (s : S) :
    ParameterSpace n →L[ℝ] ℝ := O s • parameter n+∑ j, V j s • coordinateProjection n j

omit [Fintype S] [Nonempty S] in
theorem siteMultiplierExponent_axis (n : ℕ) (V : Fin n → S → ℝ) (O : S → ℝ) (s : S) :
    siteMultiplierExponent n V O s (parameterAxis n)=O s := by
  simp [siteMultiplierExponent,parameter_axis,coordinateProjection_axis]

omit [Nonempty S] in
theorem siteMultiplier_terminal (n : ℕ) (V : Fin n → S → ℝ) (O c : S → ℝ) :
    affineLogPartition c (siteMultiplierExponent n V O)=fun z =>
      siteValueTerminal c (parameter n z • O+∑ j, coordinateProjection n j z • V j) := by
  funext z
  simp only [affineLogPartition,siteValueTerminal,siteMultiplierExponent,add_apply,smul_apply,
    smul_eq_mul,sum_apply,ContinuousLinearMap.proj_apply,Pi.add_apply,Pi.smul_apply,Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  congr 2
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

theorem siteMultiplier_terminal_gradient (n : ℕ) (V : Fin n → S → ℝ) (O c : S → ℝ) :
    rootGradient n (affineLogPartition c (siteMultiplierExponent n V O))=fun z =>
      affineMoment c (fun s => ContinuousLinearMap.proj s) O
        (parameter n z • O+∑ j, coordinateProjection n j z • V j) := by
  funext z
  rw [rootGradient,fderiv_affineLogPartition_apply]
  simp only [affineMoment,affineGibbs,siteMultiplierExponent,
    add_apply,smul_apply,smul_eq_mul,sum_apply,ContinuousLinearMap.proj_apply,Pi.add_apply,
    Pi.smul_apply,Finset.sum_apply]
  have he (s : S) : O s*parameter n z+∑ j, V j s*coordinateProjection n j z=
      parameter n z*O s+∑ j, coordinateProjection n j z*V j s := by
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  simp only [he,parameter_axis,coordinateProjection_axis,mul_one,mul_zero,Finset.sum_const_zero,add_zero]

omit [Nonempty S] in
theorem siteValueTerminal_add_multiplier (c O : S → ℝ) (L : ℝ) :
    siteValueTerminal (fun s => c s+L*O s)=fun z => siteValueTerminal c (L • O+z) := by
  funext z
  simp only [siteValueTerminal,affineLogPartition,ContinuousLinearMap.proj_apply,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_assoc]

theorem vectorHierarchy_bounded_multiplier (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (V : Fin n → S → ℝ) (c O : S → ℝ)
    (hO : ∀ s, |O s|≤1) (L : ℝ) :
    vectorHierarchy n m V (siteValueTerminal (fun s => c s+L*O s)) 0 ≤
      vectorHierarchy n m V (siteValueTerminal c) 0+
      L*vectorHierarchyAverage n m V (siteValueTerminal c)
        (affineMoment c (fun s => ContinuousLinearMap.proj s) O) 0+L^2/2 := by
  have H := hierarchy_bounded_observable_quadratic n m hm c (siteMultiplierExponent n V O)
    (fun s => by rw [siteMultiplierExponent_axis]; exact hO s) L
  rw [funext (hierarchyPressure_rootGradient n m (affineLogPartition_boundedDerivs _ _)),
    siteMultiplier_terminal_gradient,siteMultiplier_terminal,
    hierarchyAverage_vector_linear n m V (siteValueTerminal c)
      (affineMoment c (fun s => ContinuousLinearMap.proj s) O) (fun x => x • O),
    hierarchyPressure_vector_linear n m V (siteValueTerminal c) (fun x => x • O)] at H
  simp only [zero_smul] at H
  rw [siteValueTerminal_add_multiplier,vectorHierarchy_translate,add_zero]
  exact H
end Site

end SK.Analytic

end
end

end OAI
