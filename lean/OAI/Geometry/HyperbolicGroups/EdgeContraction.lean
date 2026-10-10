import Mathlib
import OAI.Geometry.HyperbolicGroups.SquarePathFilling

namespace OAI

section


/-! In a genuinely simply connected space, individual graph edges contract
with arbitrary prescribed vertex tracks. -/
noncomputable section
open scoped Topology unitInterval
namespace HyperbolicObstruction.EdgeContraction
variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
  {a b z : X} (p : Path a b) (pa : Path a z) (pb : Path b z)

def square : C(I × I,X) := SquarePathFilling.fill
  (SimplyConnectedSpace.paths_homotopic (p.trans pb) (pa.trans (Path.refl z))).some

def contraction : C(I × I,X) := (square p pa pb).comp ⟨Prod.swap,continuous_swap⟩
@[simp] lemma contraction_initial (s : I) : contraction p pa pb (0,s) = p s :=
  SquarePathFilling.fill_bottom _ s
@[simp] lemma contraction_final (s : I) : contraction p pa pb (1,s) = z :=
  SquarePathFilling.fill_top _ s
@[simp] lemma contraction_left (t : I) : contraction p pa pb (t,0) = pa t :=
  SquarePathFilling.fill_left _ t
@[simp] lemma contraction_right (t : I) : contraction p pa pb (t,1) = pb t :=
  SquarePathFilling.fill_right _ t

end HyperbolicObstruction.EdgeContraction
end
end

section

end

end OAI
