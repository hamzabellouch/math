import OAI.Analysis.Nonexpansive.TreeProducer
import OAI.Analysis.Nonexpansive.TreeFiniteWitness
import OAI.Analysis.Nonexpansive.BranchContradiction

namespace OAI

/-!
# The actual tree and switching contradiction for normalized minimal data

The adaptive producer constructs the tree without an added geometric premise.
Its actual finite switching witnesses lie in the whole difference ball, and
the branch argument contradicts the produced dense-point detectors there.
-/

noncomputable section

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace SwitchingTreeData

/-- The concrete constructed tree cannot coexist with normalized minimal data. -/
theorem contradiction {D : NormalizedMinimalData (X := X)} (A : SwitchingTreeData D) :
    False := by
  apply tree_finite_witnesses_contradiction D A.tree A.functionalAt A.nodeLabel A.budget
  · intro k hk v
    exact A.functionalAt_norm k v
  · intro k hk v i hi
    cases k with
    | zero => omega
    | succ k => exact A.dense_detector k v i hi
  · exact A.summable_budget
  · intro n hn
    exact A.finite_witness n

end SwitchingTreeData

/-- No normalized minimal invariant counterexample exists. This calls the
actual adaptive-tree producer and the fully discharged finite switching proof. -/
theorem normalizedMinimalData_false (D : NormalizedMinimalData (X := X)) : False := by
  obtain ⟨A⟩ := exists_switchingTreeData D
  exact A.contradiction

end ReflexiveFixedPoints

end

end OAI
