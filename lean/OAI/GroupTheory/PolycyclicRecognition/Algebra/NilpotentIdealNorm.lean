import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentIdealDerivation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealNormedLieAlgebra

namespace OAI

/-! # A compatible norm on the codimension-one ideal -/

noncomputable section
namespace PolycyclicRecognition.LieCodimensionOneData

variable {L : Type*} [RealNormedLieAlgebra L] (C : LieCodimensionOneData L)

@[instance_reducible]
def normedIdeal : RealNormedLieAlgebra C.ideal := by
  let : NormedAddCommGroup C.ideal := NormedAddCommGroup.induced C.ideal L
    C.ideal.incl Subtype.val_injective
  let : NormedSpace ℝ C.ideal := NormedSpace.induced ℝ C.ideal L C.ideal.incl.toLinearMap
  exact { (inferInstance : NormedAddCommGroup C.ideal),
    (inferInstance : LieRing C.ideal), (inferInstance : NormedSpace ℝ C.ideal),
    (inferInstance : LieAlgebra ℝ C.ideal) with }

end PolycyclicRecognition.LieCodimensionOneData

end

end OAI
