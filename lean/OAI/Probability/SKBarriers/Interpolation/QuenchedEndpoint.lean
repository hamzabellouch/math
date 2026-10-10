import Mathlib
import OAI.Probability.SKBarriers.Interpolation.ZeroFieldEndpoint
import OAI.Probability.SKBarriers.Calculus.CoordinateGaussianLaw

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem spinExponent_sk_eq (N : ℕ) (β : ℝ) (s : Config N)
    (z : ParameterSpace (Fintype.card (Edge N))) :
    spinExponent (Fintype.card (Edge N)) (fun _ => β/Real.sqrt (N:ℝ)) (skInteraction N) s z =
      β*hamiltonian (enumeratedDisorder N z) s := by
  simp only [spinExponent,coordinateLinear_apply,spinMonomial_skInteraction,hamiltonian,
    enumeratedDisorder]
  rw [← (Fintype.equivFin (Edge N)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  simp only [Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem affineLogPartition_sk_eq (N : ℕ) (β : ℝ)
    (z : ParameterSpace (Fintype.card (Edge N))) :
    affineLogPartition (fun _ : Config N => 0)
      (spinExponent (Fintype.card (Edge N)) (fun _ => β/Real.sqrt (N:ℝ)) (skInteraction N)) z =
      logPartition β (enumeratedDisorder N z) := by
  simp only [affineLogPartition,spinExponent_sk_eq,zero_add,logPartition,partition]

theorem skBlockRoot_zero_fields_eq (N k : ℕ) (β : ℝ) :
    skBlockRoot N k β (fun _ => 0) = ∫ J, logPartition β J ∂disorderLaw N := by
  rw [skBlockRoot_zero_fields]
  simp only [affineLogPartition_sk_eq]
  have H := enumeratedDisorder_measurePreserving N 0
  rw [← H.map_eq,integral_map H.measurable.aemeasurable (continuous_logPartition β).aestronglyMeasurable]
end SK.Analytic

end
end

end

end OAI
