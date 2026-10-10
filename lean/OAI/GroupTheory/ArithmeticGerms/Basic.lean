import Mathlib

namespace OAI

/-! Finite-index virtual isomorphism graphs. -/



namespace ArithmeticGerms
variable {G H : Type*} [Group G] [Group H]
structure VirtualGraph (G H : Type*) [Group G] [Group H] where
  graph : Subgroup (G × H)
  fst_injective : Function.Injective ((MonoidHom.fst G H).comp graph.subtype)
  snd_injective : Function.Injective ((MonoidHom.snd G H).comp graph.subtype)
  fst_finite : (graph.map (MonoidHom.fst G H)).FiniteIndex
  snd_finite : (graph.map (MonoidHom.snd G H)).FiniteIndex

attribute [instance] VirtualGraph.fst_finite VirtualGraph.snd_finite

namespace VirtualGraph

variable (C : VirtualGraph G H)

@[ext]
theorem ext {C D : VirtualGraph G H} (h : C.graph = D.graph) : C = D := by
  cases C
  cases D
  cases h
  rfl

abbrev domain : Subgroup G := C.graph.map (MonoidHom.fst G H)

abbrev codomain : Subgroup H := C.graph.map (MonoidHom.snd G H)

end VirtualGraph
end ArithmeticGerms

end OAI
