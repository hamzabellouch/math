import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryInverseShadow

namespace OAI

/-! # Continuous boundary maps with one compact shadow -/

noncomputable section
namespace PolycyclicRecognition

/-- Data constructed by the ray-limit theorem. The compact set is common
to all maps in the family and all ambient basepoints. -/
structure BoundaryMapFamily {P G S T : Type*} [Group G]
    [One S] [TopologicalSpace S] [One T] [TopologicalSpace T]
    (actS : G →* Equiv.Perm S) (actT : G →* Equiv.Perm T) (f : P → G → G) where
  map : P → S → T
  compact : Set T
  isCompact : IsCompact compact
  continuous : ∀ p, Continuous (map p)
  shadow : ∀ p x, ∃ z ∈ compact, map p (actS x 1) = actT (f p x) z

end PolycyclicRecognition

end

end OAI
