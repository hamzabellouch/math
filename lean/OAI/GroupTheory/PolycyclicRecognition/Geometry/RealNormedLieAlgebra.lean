import Mathlib.Algebra.Lie.Basic
import Mathlib.Analysis.Normed.Module.Basic

namespace OAI

/-! # Compatible normed and Lie structures

Bundling the shared additive and scalar structures avoids two unrelated
copies of those structures in differentiating a Lie polynomial.
-/

namespace PolycyclicRecognition

class RealNormedLieAlgebra (L : Type*) extends NormedAddCommGroup L, LieRing L,
    NormedSpace ℝ L, LieAlgebra ℝ L

end PolycyclicRecognition

end OAI
