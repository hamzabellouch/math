import OAI.Analysis.Nuclearity.NuclearTensorFunctional
import OAI.Analysis.OperatorAlgebra.CyclicCoefficientApproximation

namespace OAI

/-! Bounded finite coefficient functionals on the completed minimal tensor
product. Their dependence on the coefficient vectors is continuous. This
allows the cyclic-vector argument to handle arbitrary finite tensor tests. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder InnerProductSpace

namespace WeakPureInfiniteness

variable {B C H I : Type*} [NonUnitalCStarAlgebra B] [CStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype I]

def operatorCoefficient (u v : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ H v)

omit [CompleteSpace H] in
lemma operatorCoefficient_apply (u v : H) (F : H →L[ℂ] H) :
    operatorCoefficient u v F = ⟪u, F v⟫_ℂ := rfl

def tensorCoefficientFunctional (f : B →L[ℂ] (H →L[ℂ] H))
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (x : I → B) (k : I → H) :
    MinimalTensor B C →L[ℂ] ℂ :=
  ∑ i, ∑ j, (operatorCoefficient (k i) (k j)).comp
    ((cpCommutingLinear f η).comp (ContinuousLinearMap.mulLeftRight ℂ (MinimalTensor B C)
      (minimalElementary (star (x i)) 1) (minimalElementary (x j) 1)))

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
lemma tensorCoefficientFunctional_apply (f : B →L[ℂ] (H →L[ℂ] H))
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (x : I → B) (k : I → H) (z : MinimalTensor B C) :
    tensorCoefficientFunctional f η x k z = ∑ i, ∑ j,
      ⟪k i, cpCommutingLinear f η
        (minimalElementary (star (x i)) 1 * z * minimalElementary (x j) 1) (k j)⟫_ℂ := by
  simp only [tensorCoefficientFunctional, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mulLeftRight_apply, operatorCoefficient_apply]

lemma tensorCoefficientFunctional_elementary (hB : Nuclear B)
    (f : B →L[ℂ] (H →L[ℂ] H)) (hf : CompletelyPositive f)
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ b c, Commute (f b) (η c))
    (x : I → B) (k : I → H) (b : B) (c : C) :
    tensorCoefficientFunctional f η x k (minimalElementary b c) =
      ∑ i, ∑ j, ⟪k i, f (star (x i) * b * x j) (η c (k j))⟫_ℂ := by
  rw [tensorCoefficientFunctional_apply]
  simp only [← minimalElementary_mul, one_mul, mul_one,
    cpCommutingLinear_elementary hB f hf η hc, mul_apply_eq_comp]

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
lemma tensorCoefficientFunctional_continuous (f : B →L[ℂ] (H →L[ℂ] H))
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (x : I → B) (z : MinimalTensor B C) :
    Continuous (fun k : I → H => tensorCoefficientFunctional f η x k z) := by
  simp only [tensorCoefficientFunctional_apply]
  fun_prop

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
theorem finite_tensor_coefficient_approximation {D J : Type*}
    [NonUnitalCStarAlgebra D] [Fintype J]
    (f : B →L[ℂ] (H →L[ℂ] H)) (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (x : I → B)
    (π : Unitization ℂ D →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcyc : DenseRange (fun a => π a ξ)) (k : I → H)
    (z : J → MinimalTensor B C) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : I → Unitization ℂ D,
      ‖(fun j => tensorCoefficientFunctional f η x k (z j)) -
        (fun j => tensorCoefficientFunctional f η x (fun i => π (a i) ξ) (z j))‖ < ε := by
  let Q : (I → H) → J → ℂ := fun k j => tensorCoefficientFunctional f η x k (z j)
  have hQ : Continuous Q := continuous_pi (fun j => tensorCoefficientFunctional_continuous f η x (z j))
  have hQat : ContinuousAt Q k := hQ.continuousAt
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hQat ε hε
  have hd : DenseRange (fun a : I → Unitization ℂ D => fun i => π (a i) ξ) :=
    DenseRange.piMap (fun _ => hcyc)
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp hd k δ hδ
  refine ⟨a, ?_⟩
  have h := hclose (by simpa only [dist_comm] using ha)
  simpa only [dist_eq_norm, norm_sub_rev, Q] using h

end WeakPureInfiniteness

end

end OAI
