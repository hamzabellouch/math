import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileScalarOverlap

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem spinExponent_oneSite (n : ℕ) (a : Fin n → ℝ) :
    spinExponent n a (fun _ => ({0}:Finset (Fin 1)))=
      fun s : Config 1 => spin (s 0) • coordinateLinear n a := by
  funext s
  ext z
  simp only [spinExponent,spinMonomial,Finset.prod_singleton,coordinateLinear_apply,
    smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem scalarMomentSquare_contDiff_coeff (n : ℕ) (m : Fin n → ℝ) (j : Fin (n+1)) :
    ContDiff ℝ 2 (fun v : Fin n → ℝ =>
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j 0) := by
  have H := spinHierarchyOverlap_contDiff n m (fun _ => ({0}:Finset (Fin 1)))
    (fun i s => spin (s i)) (by intro i s; cases s i <;> norm_num [spin]) j
  simpa only [spinExponent_oneSite,hierarchyMeanOverlap_oneSite] using H

end SK.Analytic

end
end

end OAI
