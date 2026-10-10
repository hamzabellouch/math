import OAI.Geometry.EinsteinFour.OrientationCoverClosed
import Mathlib.Topology.Connected.Clopen

namespace OAI

/-! A disconnected two-sheeted orientation cover has a continuous global sheet. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set Function Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
theorem orientationCover_image_clopen {U : Set (OrientationCover M)} (hU : IsClopen U) :
    IsClopen (orientationCoverProjection '' U) := by
  refine ⟨?_, ?_⟩
  · exact (hU.isClosed.isCompact.image orientationCover_isCoveringMap.continuous).isClosed
  · exact orientationCover_isCoveringMap.isLocalHomeomorph.isOpenMap U hU.isOpen

theorem orientationCover_clopen_surjective {U : Set (OrientationCover M)}
    (hU : IsClopen U) (hne : U.Nonempty) :
    orientationCoverProjection '' U = univ :=
  (orientationCover_image_clopen hU).eq_univ (hne.image _)

theorem orientationCover_clopen_deck_notMem {U : Set (OrientationCover M)}
    (hU : IsClopen U) (hproper : Uᶜ.Nonempty) {x : OrientationCover M} (hx : x ∈ U) :
    orientationCoverDeck x ∉ U := by
  have himage := orientationCover_clopen_surjective hU.compl hproper
  have hm : x.proj ∈ orientationCoverProjection '' Uᶜ := by rw [himage]; trivial
  obtain ⟨z, hz, hp⟩ := hm
  rcases (orientationCover_fibers z x).mp hp with h | h
  · exact False.elim (hz (h ▸ hx))
  · exact h ▸ hz

theorem orientationCover_clopen_projection_bijective {U : Set (OrientationCover M)}
    (hU : IsClopen U) (hne : U.Nonempty) (hproper : Uᶜ.Nonempty) :
    Bijective (fun x : U => (x.val).proj) := by
  constructor
  · intro x y h
    apply Subtype.ext
    rcases (orientationCover_fibers x.val y.val).mp h with h | h
    · exact h
    · exact False.elim (orientationCover_clopen_deck_notMem hU hproper y.property
        (h ▸ x.property))
  · intro x
    have hm : x ∈ orientationCoverProjection '' U := by
      rw [orientationCover_clopen_surjective hU hne]
      trivial
    obtain ⟨y, hy, hp⟩ := hm
    exact ⟨⟨y, hy⟩, hp⟩

theorem exists_orientationCover_section_of_clopen {U : Set (OrientationCover M)}
    (hU : IsClopen U) (hne : U.Nonempty) (hproper : Uᶜ.Nonempty) :
    ∃ s : M → OrientationCover M, Continuous s ∧ ∀ x, (s x).proj = x := by
  let e : U ≃ M := Equiv.ofBijective (fun x : U => x.val.proj)
    (orientationCover_clopen_projection_bijective hU hne hproper)
  have hc : Continuous e := orientationCover_isCoveringMap.continuous.comp continuous_subtype_val
  have ho : IsOpenMap e :=
    orientationCover_isCoveringMap.isLocalHomeomorph.isOpenMap.comp hU.isOpen.isOpenMap_subtype_val
  let H := e.toHomeomorphOfContinuousOpen hc ho
  refine ⟨fun x => (H.symm x).val, continuous_subtype_val.comp H.symm.continuous, ?_⟩
  intro x
  exact H.apply_symm_apply x

end
end PositiveEinsteinFour.Geometry

end OAI
