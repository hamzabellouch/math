import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.RawNormal

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

lemma rawPair_sub (a b : TwoForm X) (z : Space) :
    rawPair J α ht p D (a-b) z = rawPair J α ht p D a z - rawPair J α ht p D b z := by
  ext i
  fin_cases i <;> rfl
end TamingCompatibility.GeometricChart

end

end OAI
