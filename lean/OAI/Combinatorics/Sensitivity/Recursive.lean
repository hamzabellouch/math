import OAI.Combinatorics.Sensitivity.RecursiveBlocks
import OAI.Combinatorics.Sensitivity.RecursiveOne
import OAI.Combinatorics.Sensitivity.RecursiveZero
import OAI.Combinatorics.Sensitivity.RecursiveJointZero

namespace OAI

/-! Four sensitivity recurrences for a regular tournament and a good labeling. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursive_four_recurrences {M r h : ℕ} {I : Type} [Fintype I]
    (T : RegularTournament M) (A : GoodLabeling T.toTournament r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r) :
    let P := recursiveFamily T.toTournament A.label F
    (sideSensitivity P true ≤ M ^ 2 * sideSensitivity F false + r * sideSensitivity F true) ∧
    (jointSensitivity P true ≤ M ^ 2 * jointSensitivity F false + r * sideSensitivity F true) ∧
    (sideSensitivity P false ≤ 16 * sideSensitivity F false + sideSensitivity F true +
      3 * jointSensitivity F true) ∧
    (jointSensitivity P false ≤ 16 * sideSensitivity F false + 3 * jointSensitivity F true) := by
  exact ⟨recursive_side_one T.toTournament A.label F (M ^ 2) T.outdegree,
    recursive_joint_one T.toTournament A.label F hF (M ^ 2) T.outdegree,
    recursive_side_zero T.toTournament A F hF hr,
    recursive_joint_zero T.toTournament A F hF hr⟩

end Paper320

end

end OAI
