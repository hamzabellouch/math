import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.GraphSeparatorTransfer
import OAI.Geometry.HyperbolicGroups.SeparatorGrouping
import OAI.Geometry.HyperbolicGroups.PictureSqrtSeparator
import OAI.Geometry.HyperbolicGroups.PictureStarGraph

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D)

/-- Literal genus-zero planar separator, independent of face degrees,
vertex degrees, all parallel copies, and the specified vertex carrier. -/
theorem planar_component_separator (hG : M.GenusZero) (hc : M.underlyingGraph.Connected)
    (U : Finset M.GraphVertex) :
    ∃ S : Finset M.GraphVertex, S ⊆ U ∧ S.card ≤ 11*Nat.sqrt U.card ∧
      ∀ W : Finset M.GraphVertex, W ⊆ U → Disjoint W S →
        (M.underlyingGraph.induce (W : Set M.GraphVertex)).Preconnected →
        2*W.card ≤ U.card := by
  have hs := M.triangulation.sqrt_component_separator (M.triangulation_genusZero hG)
    (M.triangulation_connected hc) 3 (fun x => (M.triangulation_face_degree x).le)
  exact component_separator_pullback M.underlyingGraph M.triangulation.underlyingGraph
    M.starOldHom M.starOldVertex_injective 11 (by simpa using hs) U

/-- A connected genus-zero rotation system has balanced separators. -/
theorem planar_balanced_separators (hG : M.GenusZero) (hc : M.underlyingGraph.Connected) :
    HasBalancedSeparators M.underlyingGraph 11 :=
  balanced_separators_of_component_separators M.underlyingGraph 11
    (M.planar_component_separator hG hc)

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
