import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalEdge

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace NerveHomology
open FreeChains
@[simp] lemma id {D:Type} [Category.{0} D] (q:ℕ) : map (𝟭 D) q=𝟙 _ := by
  change SSet.homologyMap (𝟙 _) Z q=𝟙 _
  exact SSet.homologyMap_id _ _ _
end NerveHomology

end

end OAI
