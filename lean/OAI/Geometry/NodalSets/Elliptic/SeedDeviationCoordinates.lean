import OAI.Geometry.NodalSets.Elliptic.SeedCoordPatchTopology
import OAI.Geometry.NodalSets.Elliptic.SeedCoordinateField
import OAI.Geometry.NodalSets.Elliptic.SeedPatchTopology

namespace OAI

namespace Yau.Target
open Manifold Set Yau.Geometry Yau.Jets
open scoped Topology
noncomputable section

def seedDeviationCoordinates (K : Set Base) : Set Coord :=
  (fun x ↦ (extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)) ⁻¹' K

lemma seedDeviationCoordinates_eq_image {K : Set Base}
    (hK : K ⊆ (extChartAt (𝓡 4) seedPoint).source) :
    seedDeviationCoordinates K =
      (fun p ↦ seedCoordEquiv.symm (extChartAt (𝓡 4) seedPoint p)) '' K := by
  ext x
  constructor
  · intro hx
    refine ⟨(extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x),hx,?_⟩
    dsimp only
    rw [(extChartAt (𝓡 4) seedPoint).right_inv
      (by rw [centeredSphereChart_target]; trivial),seedCoordEquiv.symm_apply_apply]
  · rintro ⟨p,hp,rfl⟩
    change (extChartAt (𝓡 4) seedPoint).symm
      (seedCoordEquiv (seedCoordEquiv.symm (extChartAt (𝓡 4) seedPoint p))) ∈ K
    rw [seedCoordEquiv.apply_symm_apply,(extChartAt (𝓡 4) seedPoint).left_inv (hK hp)]
    exact hp

lemma seedDeviationCoordinates_compact {K : Set Base} (hK : IsCompact K)
    (hchart : K ⊆ (extChartAt (𝓡 4) seedPoint).source) :
    IsCompact (seedDeviationCoordinates K) := by
  rw [seedDeviationCoordinates_eq_image hchart]
  exact hK.image_of_continuousOn (seedCoordEquiv.symm.continuous.comp_continuousOn
    ((continuousOn_extChartAt seedPoint).mono hchart))

lemma seedDeviationCoordinates_subset_patch {K : Set Base} {r : ℝ}
    (hK : K ⊆ seedSpherePatch r) : seedDeviationCoordinates K ⊆ seedCoordPatch r := by
  intro x hx
  obtain ⟨y,hy,he⟩ := hK hx
  have ht : seedCoordEquiv x ∈ (extChartAt (𝓡 4) seedPoint).target := by
    rw [centeredSphereChart_target]; trivial
  have hy' : y ∈ (extChartAt (𝓡 4) seedPoint).target := by
    rw [centeredSphereChart_target]; trivial
  have heq : y = seedCoordEquiv x :=
    (extChartAt (𝓡 4) seedPoint).symm.injOn hy' ht he
  simpa only [seedCoordPatch,mem_preimage,← heq] using hy

lemma seedDeviationCoordinates_inverse_image {K : Set Base}
    (hK : K ⊆ (extChartAt (𝓡 4) seedPoint).source) :
    (fun x ↦ (extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)) ''
      seedDeviationCoordinates K = K := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact hx
  · intro p hp
    refine ⟨seedCoordEquiv.symm (extChartAt (𝓡 4) seedPoint p),?_,?_⟩
    · change (extChartAt (𝓡 4) seedPoint).symm
        (seedCoordEquiv (seedCoordEquiv.symm (extChartAt (𝓡 4) seedPoint p))) ∈ K
      rw [seedCoordEquiv.apply_symm_apply,(extChartAt (𝓡 4) seedPoint).left_inv (hK hp)]
      exact hp
    · dsimp only
      rw [seedCoordEquiv.apply_symm_apply,(extChartAt (𝓡 4) seedPoint).left_inv (hK hp)]

end
end Yau.Target

end OAI
