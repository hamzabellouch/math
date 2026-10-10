import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.OrientedTreeDomains

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
private def emptyTreeMessage {I : Type} (b : BinaryTree I) (h : b=.nil)
    (t : OrientedPivotTreeTape f r b) (C : PivotContext K V) : OrientedPivotTreeMessage f r b t C := by
  subst b
  exact PUnit.unit
omit [Finite K] in
private lemma emptyTreeCost {I : Type} (b : BinaryTree I) (h : b=.nil)
    (t : OrientedPivotTreeTape f r b) (C : PivotContext K V)
    (m : OrientedPivotTreeMessage f r b t C) : orientedPivotSlotCost f r b t C m=0 := by
  subst b
  rfl

def variableTreeEmpty {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V) :
    VariableTreeMessage f r t C :=
  ⟨⟨0,Nat.zero_lt_succ w⟩,emptyTreeMessage f r (finiteBalanced 0)
    (by simp [finiteBalanced,balanced,BinaryTree.map]) _ C⟩
omit [Finite K] in
lemma variableTreeEmpty_cost {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V) :
    variableTreeCost f r t C (variableTreeEmpty f r t C)=Real.log (w+1) := by
  unfold variableTreeCost variableTreeEmpty
  dsimp only
  rw [emptyTreeCost f r (finiteBalanced 0) (by simp [finiteBalanced,balanced,BinaryTree.map])]
  exact add_zero _
omit [Finite K] in
lemma variableTreeEmpty_domain {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V)
    (j : Fin (w+1)) : variableTreeDomain f r t C (variableTreeEmpty f r t C) j=∅ := by
  simp [variableTreeDomain,variableTreeEmpty]
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
