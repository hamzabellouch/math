import OAI.GroupTheory.PolycyclicRecognition.Geometry.AbelianLieModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianDynkinInput
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentIdealDerivation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialDerivationAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentDerivationFlowDerivative
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentSemidirectGroup
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentLieExistenceConstruction

/-! # Concrete steps in nilpotent Lie model construction

The abelian case, codimension-one splitting, polynomial derivation actions
and the actual semidirect tangent bracket give model existence by dimension
induction. Only finite BCH on the already constructed smaller models remains
an input.
-/
