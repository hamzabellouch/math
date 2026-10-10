import OAI.Analysis.Nuclearity.UnitizedAbelianClosure
import OAI.Analysis.PureInfiniteness.ApproximatelyInnerCP

namespace OAI

/-! Continuous linear maps realizing the finite coefficient formulas. For
the abelian coefficient cone their complete positivity follows from the
proved finite inner approximation, rather than an extra cone assumption. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {B D I : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]
  [Fintype I]

def unitizedRightOperator (a : Unitization ℂ D) : D →L[ℂ] D :=
  a.fst • ContinuousLinearMap.id ℂ D + (ContinuousLinearMap.mul ℂ D).flip a.snd

def unitizedLeftOperator (a : Unitization ℂ D) : D →L[ℂ] D :=
  a.fst • ContinuousLinearMap.id ℂ D + ContinuousLinearMap.mul ℂ D a.snd

lemma unitizedRightOperator_apply (a : Unitization ℂ D) (x : D) :
    unitizedRightOperator a x = unitizedRightMul x a := rfl

lemma unitizedLeftOperator_apply (a : Unitization ℂ D) (x : D) :
    unitizedLeftOperator a x = unitizedLeftMul a x := rfl

def unitizedCoefficientMap (T : B →L[ℂ] D) (a : I → Unitization ℂ D) (c : I → B) :
    B →L[ℂ] D :=
  ∑ i, ∑ j, (unitizedRightOperator (a j)).comp
    ((unitizedLeftOperator (star (a i))).comp
      (T.comp (ContinuousLinearMap.mulLeftRight ℂ B (star (c i)) (c j))))

lemma unitizedCoefficientMap_apply (T : B →L[ℂ] D) (a : I → Unitization ℂ D)
    (c : I → B) (b : B) :
    unitizedCoefficientMap T a c b = unitizedCoefficientEnlargement T a c b := by
  simp only [unitizedCoefficientMap, sum_apply, ContinuousLinearMap.comp_apply,
    unitizedRightOperator_apply, unitizedLeftOperator_apply,
    ContinuousLinearMap.mulLeftRight_apply, unitizedCoefficientEnlargement,
    unitizedSandwich]

lemma ApproximatelyOneStepAlong.approximatelyInner (β : B →⋆ₙₐ[ℂ] D)
    {T : B → D} (hT : ApproximatelyOneStepAlong β T) : ApproximatelyInnerAlong β T := by
  intro F ε hε
  obtain ⟨v, hv⟩ := hT F ε hε
  refine ⟨1, fun _ => v, ?_⟩
  intro b hb
  simpa only [Fin.sum_univ_one] using hv b hb

variable {A : Type*} [NonUnitalCStarAlgebra A]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem finiteUnitizedAbelianCoefficientCone_has_cp_map (hP : MainGap.PropertyP A)
    (β : B →⋆ₙₐ[ℂ] N) {S : B → N}
    (hS : S ∈ finiteUnitizedAbelianCoefficientCone U β) :
    ∃ T : B →L[ℂ] N, (∀ b, T b = S b) ∧ CompletelyPositive T := by
  obtain ⟨n, m, V, hinner, hpos, hcomm, a, c, hval⟩ := hS
  let T : B →L[ℂ] N := ∑ j, unitizedCoefficientMap (V j)
    (fun i => a (j, i)) (fun i => c (j, i))
  have hTS (b : B) : T b = S b := by
    simp only [T, sum_apply, unitizedCoefficientMap_apply, hval b]
  refine ⟨T, hTS, ?_⟩
  apply ApproximatelyInnerAlong.completelyPositive β
  apply ApproximatelyOneStepAlong.approximatelyInner β
  have h := approximately_oneStepAlong_unitized_finite_coefficient_sum U hP β V
    hinner hpos hcomm a c
  have he : (T : B → N) = fun b => ∑ j, unitizedCoefficientEnlargement (V j)
      (fun i => a (j, i)) (fun i => c (j, i)) b := by
    funext b
    simp only [T, sum_apply, unitizedCoefficientMap_apply]
  rw [he]
  exact h

end WeakPureInfiniteness

end

end OAI
