import OAI.Analysis.Nuclearity.CommutantNullCone
import OAI.Analysis.PureInfiniteness.CoefficientConeClosure

namespace OAI

/-! Application of the tensor-ideal step to the actual point-norm cone.
The elementary-span property of the GNS common-null ideals
(Blackadar 3.3 / Tomiyama 5) supplies coefficient approximation. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

universe u v

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem inclusion_mem_coefficientClosure_of_elementary_span
    (hP : MainGap.PropertyP A) (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] N)
    (hspan : ∀ (I : Type v) [Fintype I]
      (l : I → selfAdjoint N →L[ℝ] ℝ) (R : FunctionalTensorRepresentation l),
        R.elementarySpan U hB β) :
    (β : B → N) ∈ closure (finiteUnitizedAbelianCoefficientCone U β) := by
  classical
  apply mem_closure_of_finite_approximation
  intro F ε hε
  let I := F × Fin 4
  let x (i : I) : selfAdjoint B :=
    ⟨fourPositiveParts i.1.val i.2, (fourPositiveParts_nonneg i.1.val i.2).isSelfAdjoint⟩
  obtain ⟨T, _, hTC, hT⟩ := finite_coefficient_approximation_of_commutant_span U
    hP hB β x (hspan I) (show 0 < ε / 5 by positivity)
  refine ⟨T, hTC, ?_⟩
  let L := starHomContinuousLinear β - T
  have he (b : F) (j : Fin 4) : ‖L (fourPositiveParts b.val j)‖ < ε / 5 := by
    have h := (norm_le_pi_norm ((fun i => β (x i)) - (fun i => T (x i))) (b, j)).trans_lt hT
    exact h
  intro b hb
  change ‖L b‖ < ε
  calc
    _ ≤ (‖L (fourPositiveParts b 0)‖ + ‖L (fourPositiveParts b 1)‖) +
        (‖L (fourPositiveParts b 2)‖ + ‖L (fourPositiveParts b 3)‖) :=
      norm_apply_le_fourPositiveParts L b
    _ < (ε / 5 + ε / 5) + (ε / 5 + ε / 5) :=
      add_lt_add (add_lt_add (he ⟨b, hb⟩ 0) (he ⟨b, hb⟩ 1))
        (add_lt_add (he ⟨b, hb⟩ 2) (he ⟨b, hb⟩ 3))
    _ < ε := by linarith

theorem approximatelyOneStepAlong_of_nuclear_and_elementary_span
    (hP : MainGap.PropertyP A) (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] N)
    (hspan : ∀ (I : Type v) [Fintype I]
      (l : I → selfAdjoint N →L[ℝ] ℝ) (R : FunctionalTensorRepresentation l),
        R.elementarySpan U hB β)
    {T : B → N} (hT : ApproximatelyInnerAlong β T) :
    ApproximatelyOneStepAlong β T :=
  unitizedAbelianCoefficientClosure_oneStep U hP β
    (coefficientConeClosure_of_approximatelyInnerAlong U β
      (inclusion_mem_coefficientClosure_of_elementary_span U hP hB β hspan) hT)

end WeakPureInfiniteness

end

end OAI
