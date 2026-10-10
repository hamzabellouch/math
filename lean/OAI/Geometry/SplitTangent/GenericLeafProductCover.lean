import Mathlib
import OAI.Geometry.SplitTangent.FiniteOpenMaps
import OAI.Geometry.SplitTangent.GenericFiniteCovering
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.GlobalTopologicalProduct

namespace OAI

/-! Generic Leaf Product Cover. -/

noncomputable section
open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (L : LeafJetAtlas S) (M : LeafJetAtlas S.swap) (e : ProjectiveEmbedding X)
  (hRC : RationallyConnected e) (hdim : 0<X.dim)

def regularLeafPairs : Set (L.CompactLeafSpace e hRC hdim × M.CompactLeafSpace e hRC hdim) :=
  FiniteOpenMaps.constantCardLocus (L.leafPair M e hRC hdim)

lemma regularLeafPairs_isOpen : IsOpen (L.regularLeafPairs M e hRC hdim) :=
  FiniteOpenMaps.constantCardLocus_isOpen _

lemma regularLeafPairs_dense : Dense (L.regularLeafPairs M e hRC hdim) := by
  apply FiniteOpenMaps.constantCardLocus_dense _ (L.isOpenMap_leafPair M e hRC hdim)
  intro q
  exact L.leafPair_fiber_finite M e hRC hdim q

lemma leafPair_genericCovering :
    IsCoveringMapOn (L.leafPair M e hRC hdim) (L.regularLeafPairs M e hRC hdim) := by
  apply FiniteOpenMaps.isCoveringMapOn_constantCardLocus _
    (L.isOpenMap_leafPair M e hRC hdim) _ (L.continuous_leafPair M e hRC hdim)
  intro q
  exact L.leafPair_fiber_finite M e hRC hdim q

lemma regularLeafPairs_nonempty : (L.regularLeafPairs M e hRC hdim).Nonempty :=
  (L.regularLeafPairs_dense M e hRC hdim).nonempty

lemma leafPair_locally_injective_of_regular {x : X.Carrier}
    (hx : L.leafPair M e hRC hdim x∈L.regularLeafPairs M e hRC hdim) :
    ∃ U : Set X.Carrier, IsOpen U ∧ x∈U ∧ Set.InjOn (L.leafPair M e hRC hdim) U := by
  apply FiniteOpenMaps.locally_injective_of_card_constant _
    (L.isOpenMap_leafPair M e hRC hdim) _ (L.continuous_leafPair M e hRC hdim) hx
  intro q
  exact L.leafPair_fiber_finite M e hRC hdim q

end SplitTangent.LeafJetAtlas

end

end OAI
