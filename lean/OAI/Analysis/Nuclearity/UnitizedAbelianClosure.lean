import OAI.Analysis.Nuclearity.UnitizedFiniteCoefficientCone
import OAI.Analysis.PureInfiniteness.OneStepPointNormClosure

namespace OAI

/-! The actual finite coefficient cone used with a cyclic representation of
the unitization, and its point-norm closure. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

def finiteUnitizedAbelianCoefficientCone (β : B →⋆ₙₐ[ℂ] N) : Set (B → N) :=
  {S | ∃ n m : ℕ, ∃ T : Fin n → B →L[ℂ] N,
    (∀ j, ApproximatelyInnerAlong β (T j)) ∧
    (∀ j b, 0 ≤ b → 0 ≤ T j b) ∧
    (∀ j b c, Commute (T j b) (T j c)) ∧
    ∃ a : Fin n × Fin m → Unitization ℂ N, ∃ c : Fin n × Fin m → B,
      ∀ b, S b = ∑ j, unitizedCoefficientEnlargement (T j)
        (fun i => a (j, i)) (fun i => c (j, i)) b}

theorem finiteUnitizedAbelianCoefficientCone_oneStep (hP : MainGap.PropertyP A)
    (β : B →⋆ₙₐ[ℂ] N) {T : B → N} (hT : T ∈ finiteUnitizedAbelianCoefficientCone U β) :
    ApproximatelyOneStepAlong β T := by
  obtain ⟨n, m, S, hinner, hpos, hcomm, a, c, hval⟩ := hT
  have h := approximately_oneStepAlong_unitized_finite_coefficient_sum U hP β S
    hinner hpos hcomm a c
  have he : T = fun b => ∑ j, unitizedCoefficientEnlargement (S j)
      (fun i => a (j, i)) (fun i => c (j, i)) b := funext hval
  rw [he]
  exact h

theorem unitizedAbelianCoefficientClosure_oneStep (hP : MainGap.PropertyP A)
    (β : B →⋆ₙₐ[ℂ] N) {T : B → N}
    (hT : T ∈ closure (finiteUnitizedAbelianCoefficientCone U β)) :
    ApproximatelyOneStepAlong β T :=
  approximatelyOneStepAlong_of_mem_closure β
    (fun _ h => finiteUnitizedAbelianCoefficientCone_oneStep U hP β h) hT

end WeakPureInfiniteness

end

end OAI
