import Mathlib
import OAI.Probability.SKBarriers.Interpolation.ZeroFieldEndpoint
import OAI.Probability.SKBarriers.Hierarchy.WeightedBlockMass
import OAI.Probability.SKBarriers.Hierarchy.BlockObservable

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {S : Type} [Fintype S] [Nonempty S]

omit [Fintype S] [Nonempty S] in
theorem blockObservable_endpoint_one {D N k : ℕ} (H : Fin D → S → ℝ)
    (F : Fin (k+1) → Fin N → S → ℝ) (s : S) (z : ParameterSpace (blockDimension D N k)) :
    observableExponent (blockDimension D N k) (blockObservable H F)
      (interpolationCoefficient (blockDimension D N k) (blockInterpolationChoice D N k) 1) s z=
      ∑ i, H i s*coordinateProjection (blockDimension D N k) (Fin.castAdd ((k+1)*N) i) z := by
  rw [observableExponent,coordinateLinear_apply,Fin.sum_univ_add]
  simp only [interpolationCoefficient,blockInterpolationChoice,blockObservable,Fin.addCases_left,
    Fin.addCases_right,ite_true,Bool.false_eq_true,ite_false,sub_self,Real.sqrt_zero,Real.sqrt_one,
    one_mul,zero_mul,Finset.sum_const_zero,add_zero]

omit [Fintype S] [Nonempty S] in
theorem blockObservable_endpoint_zero {D N k : ℕ} (H : Fin D → S → ℝ)
    (F : Fin (k+1) → Fin N → S → ℝ) (s : S) (z : ParameterSpace (blockDimension D N k)) :
    observableExponent (blockDimension D N k) (blockObservable H F)
      (interpolationCoefficient (blockDimension D N k) (blockInterpolationChoice D N k) 0) s z=
      ∑ b, ∑ i, F b i s*coordinateProjection (blockDimension D N k) (fieldIndex D N k b i) z := by
  rw [observableExponent,coordinateLinear_apply,Fin.sum_univ_add]
  simp only [interpolationCoefficient,blockInterpolationChoice,blockObservable,Fin.addCases_left,
    Fin.addCases_right,ite_true,Bool.false_eq_true,ite_false,sub_zero,Real.sqrt_zero,Real.sqrt_one,
    one_mul,zero_mul,Finset.sum_const_zero,zero_add]
  rw [← finProdFinEquiv.sum_comp (fun t : Fin ((k+1)*N) =>
    F (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2 s*
      coordinateProjection (blockDimension D N k) (Fin.natAdd D t) z)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,fieldIndex_eq_natAdd]

theorem blockObservable_root_one {D N k : ℕ} (H : Fin D → S → ℝ)
    (F : Fin (k+1) → Fin N → S → ℝ) (c : S → ℝ) (w : Fin (k+1) → ℝ) :
    hierarchyPressure (blockDimension D N k) (weightedBlockMass D N k w)
      (affineLogPartition c (observableExponent (blockDimension D N k) (blockObservable H F)
        (interpolationCoefficient (blockDimension D N k) (blockInterpolationChoice D N k) 1))) 0=
      ∫ z, affineLogPartition c (fun s => coordinateLinear D (fun i => H i s)) z ∂fiberGaussian D 0 := by
  rw [hierarchyPressure_split]
  have he : (fun z => affineLogPartition c
      (observableExponent (blockDimension D N k) (blockObservable H F)
        (interpolationCoefficient (blockDimension D N k) (blockInterpolationChoice D N k) 1))
          (parameterAppend D ((k+1)*N) z))=
      fun z => affineLogPartition c (fun s => coordinateLinear D (fun i => H i s))
        (cascadeRoot (E:=ParameterSpace D) ((k+1)*N) z) := by
    funext z
    simp only [affineLogPartition,blockObservable_endpoint_one,coordinateProjection_append_prefix,
      coordinateLinear_apply]
  rw [he,cascadePressure_root]
  simp only [weightedBlockMass_at_disorder]
  exact hierarchyPressure_zero D _ (affineLogPartition_boundedDerivs _ _) 0
end
end SK.Analytic

end
end

end OAI
