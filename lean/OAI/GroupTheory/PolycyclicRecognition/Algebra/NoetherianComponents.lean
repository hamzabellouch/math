import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Connected.Clopen

namespace OAI

/-! # Finitely many connected components in a Noetherian space

Each irreducible component lies in one connected component, and every
point lies in an irreducible component. The finite irreducible-component
cover therefore gives finitely many connected components.
-/

noncomputable section
namespace PolycyclicRecognition

variable {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X]

theorem finite_connectedComponents_of_noetherian : Finite (ConnectedComponents X) := by
  classical
  let I := irreducibleComponents X
  have hI : I.Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  let : Finite I := hI
  let point (s : I) : X := s.property.prop.nonempty.choose
  have hpoint (s : I) : point s ∈ (s : Set X) := s.property.prop.nonempty.choose_spec
  let q : I → ConnectedComponents X := fun s => ConnectedComponents.mk (point s)
  apply Finite.of_surjective q
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  let s : I := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  refine ⟨s, ?_⟩
  apply ConnectedComponents.coe_eq_coe'.mpr
  exact s.property.prop.2.isPreconnected.subset_connectedComponent
    mem_irreducibleComponent (hpoint s)

theorem isOpen_connectedComponent_of_noetherian (x : X) :
    IsOpen (connectedComponent x) := by
  let : Finite (ConnectedComponents X) := finite_connectedComponents_of_noetherian
  let : T1Space (ConnectedComponents X) := by
    constructor
    intro c
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    apply ConnectedComponents.isQuotientMap_coe.isCoinducing.isClosed_preimage.mp
    have he : ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk y} =
        connectedComponent y := by
      ext z
      exact ConnectedComponents.coe_eq_coe'
    rw [he]
    exact isClosed_connectedComponent
  have he : ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x} =
      connectedComponent x := by
    ext y
    exact ConnectedComponents.coe_eq_coe'
  rw [← he]
  exact (isOpen_discrete _).preimage ConnectedComponents.continuous_coe

end PolycyclicRecognition

end

end OAI
