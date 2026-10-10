import OAI.Geometry.NodalSets.Charts.ManifoldCompactExtension
import OAI.Geometry.NodalSets.Charts.SphereChartTransition
import OAI.Geometry.NodalSets.Elliptic.SeedPatchTopology

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable (center : Base)

def sphereChartToCoord (p : Base) : Yau.Jets.Coord :=
  seedCoordEquiv.symm ((extChartAt (𝓡 4) center) p)

lemma sphereChartToCoord_from (x : Yau.Jets.Coord) :
    sphereChartToCoord center (sphereChartCoordMap center x) = x := by
  unfold sphereChartToCoord sphereChartCoordMap
  rw [(extChartAt (𝓡 4) center).right_inv (by rw [centeredSphereChart_target]; trivial)]
  exact seedCoordEquiv.symm_apply_apply x

lemma sphereChartCoordMap_to {p : Base} (hp : p ∈ (extChartAt (𝓡 4) center).source) :
    sphereChartCoordMap center (sphereChartToCoord center p) = p := by
  unfold sphereChartToCoord sphereChartCoordMap
  rw [seedCoordEquiv.apply_symm_apply,(extChartAt (𝓡 4) center).left_inv hp]

theorem sphere_chart_scalar_extension (v : Yau.Jets.Coord → ℝ) (hv : ContDiff ℝ ∞ v)
    (hc : HasCompactSupport v) :
    ∃ F : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ F ∧
      tsupport F ⊆ sphereChartCoordMap center '' tsupport v ∧
      ∀ x, F (sphereChartCoordMap center x) = v x := by
  let K := sphereChartCoordMap center '' tsupport v
  have hK : IsCompact K := hc.image (sphereChartCoordMap_smooth center).continuous
  have hKU : K ⊆ (extChartAt (𝓡 4) center).source := by
    rintro p ⟨x,hx,rfl⟩
    exact sphereChartCoordMap_source center x
  have hU : IsOpen (extChartAt (𝓡 4) center).source := isOpen_extChartAt_source center
  obtain ⟨b,hb,hbc,hbs,hbr,hb1⟩ := manifold_compact_smooth_cutoff (I := 𝓡 4) hK hU hKU
  let F : Base → ℝ := fun p ↦ b p*v (sphereChartToCoord center p)
  have hF : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ F := by
    intro p
    by_cases hp : p ∈ tsupport b
    · have hcoord : ContMDiffAt (𝓡 4) 𝓘(ℝ,Yau.Jets.Coord) ∞ (sphereChartToCoord center) p :=
        seedCoordEquiv.symm.contDiff.contMDiff.contMDiffAt.comp p
          (contMDiffAt_extChartAt' (by simpa using hbs hp))
      exact (hb p).mul (hv.contMDiff.contMDiffAt.comp p hcoord)
    · apply (contMDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with z hz
      simp [F,hz]
  have hs : tsupport F ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro p hp
    have hbne : b p ≠ 0 := fun h ↦ hp (by simp [F,h])
    have hvne : v (sphereChartToCoord center p) ≠ 0 := fun h ↦ hp (by simp [F,h])
    exact ⟨sphereChartToCoord center p,subset_closure hvne,
      sphereChartCoordMap_to center (hbs (subset_closure hbne))⟩
  refine ⟨F,hF,hs,?_⟩
  intro x
  dsimp [F]
  rw [sphereChartToCoord_from]
  by_cases hx : v x = 0
  · simp [hx]
  · have h := (hb1 (sphereChartCoordMap center x) ⟨x,subset_closure hx,rfl⟩).eq_of_nhds
    rw [h,one_mul]

end
end Yau.Target

end OAI
