import OAI.Analysis.Pureness.Operators.FiniteRegularMatrixModel
import OAI.Analysis.Pureness.GroupAlgebra.GroupTraceReconstruction

namespace OAI
noncomputable section
namespace CuntzPureness
local instance freeGroupMatrixApproximationDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
open scoped lp InnerProductSpace ComplexOrder

instance freeGroupNatCountable : Countable (FreeGroup ℕ) :=
  inferInstanceAs (Countable (Quot (@FreeGroup.Red.Step ℕ)))
instance freeGroupNatResiduallyFinite : Group.ResiduallyFinite (FreeGroup ℕ) :=
  freeGroup_residuallyFinite

abbrev ReducedFreeGroup := reducedGroupAlgebra (FreeGroup ℕ)

abbrev FreeGroupMatrixIndex (n : ℕ) := SeparatingFiniteQuotient (FreeGroup ℕ) n

def freeGroupMatrixModel (n : ℕ) : FreeGroup ℕ →* unitary
    (CStarMatrix (FreeGroupMatrixIndex n) (FreeGroupMatrixIndex n) ℂ) :=
  separatingMatrixModel (FreeGroup ℕ) n

lemma freeGroupMatrixModel_norm (n : ℕ) (g : FreeGroup ℕ) :
    ‖(freeGroupMatrixModel n g : CStarMatrix (FreeGroupMatrixIndex n) (FreeGroupMatrixIndex n) ℂ)‖ = 1 :=
  separatingMatrixModel_norm (FreeGroup ℕ) n g

theorem freeGroupMatrixModel_trace (g : FreeGroup ℕ) :
    ∀ᶠ n in Filter.atTop,
      (matrixTracialState (ι := FreeGroupMatrixIndex n) complexScalarTracialState).functional
        (freeGroupMatrixModel n g) =
      (reducedGroupTracialState (FreeGroup ℕ)).functional (reducedGroupUnitary (FreeGroup ℕ) g) := by
  have h := separatingMatrixModel_trace_eventually (FreeGroup ℕ) g
  have he : (reducedGroupTracialState (FreeGroup ℕ)).functional
      (reducedGroupUnitary (FreeGroup ℕ) g) = if g=1 then 1 else 0 :=
    groupVacuumFunctional_generator (FreeGroup ℕ) g
  rwa [he]

theorem freeGroupMatrixModel_finite_moments (S : Finset (FreeGroup ℕ)) :
    ∀ᶠ n in Filter.atTop, ∀ g ∈ S,
      (matrixTracialState (ι := FreeGroupMatrixIndex n) complexScalarTracialState).functional
        (freeGroupMatrixModel n g) =
      (reducedGroupTracialState (FreeGroup ℕ)).functional (reducedGroupUnitary (FreeGroup ℕ) g) :=
  (S.eventually_all).2 (fun g _ => freeGroupMatrixModel_trace g)

theorem freeGroupMatrixModel_polynomial_trace (S : Finset (FreeGroup ℕ)) (c : FreeGroup ℕ → ℂ) :
    ∀ᶠ n in Filter.atTop,
      (matrixTracialState (ι := FreeGroupMatrixIndex n) complexScalarTracialState).functional
        (∑ g ∈ S, c g • (freeGroupMatrixModel n g :
          CStarMatrix (FreeGroupMatrixIndex n) (FreeGroupMatrixIndex n) ℂ)) =
      (reducedGroupTracialState (FreeGroup ℕ)).functional
        (∑ g ∈ S, c g • (reducedGroupUnitary (FreeGroup ℕ) g : ReducedFreeGroup)) := by
  filter_upwards [freeGroupMatrixModel_finite_moments S] with n hn
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl (fun g hg => congrArg (c g • ·) (hn g hg))

theorem reducedFreeGroup_trace_faithful (a : ReducedFreeGroup) :
    (reducedGroupTracialState (FreeGroup ℕ)).functional (star a*a)=0 ↔ a=0 :=
  reducedGroupTracialState_faithful (FreeGroup ℕ) a
end CuntzPureness

end

end OAI
