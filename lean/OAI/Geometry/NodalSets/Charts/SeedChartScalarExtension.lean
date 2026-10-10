import OAI.Geometry.NodalSets.Charts.ManifoldCompactExtension
import OAI.Geometry.NodalSets.Elliptic.SeedCoordinateField
import OAI.Geometry.NodalSets.Elliptic.SeedPatchTopology

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def seedSphereFromCoord (x : Yau.Jets.Coord) : Base :=
  (extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)

def seedSphereToCoord (p : Base) : Yau.Jets.Coord :=
  seedCoordEquiv.symm ((extChartAt (𝓡 4) seedPoint) p)

lemma seedSphereFromCoord_continuous : Continuous seedSphereFromCoord :=
  seedSphereChart_inverse_continuous.comp seedCoordEquiv.continuous

lemma seedSphereFromCoord_source (x : Yau.Jets.Coord) :
    seedSphereFromCoord x ∈ (extChartAt (𝓡 4) seedPoint).source :=
  (extChartAt (𝓡 4) seedPoint).map_target (by rw [centeredSphereChart_target]; trivial)

lemma seedSphereToCoord_from (x : Yau.Jets.Coord) :
    seedSphereToCoord (seedSphereFromCoord x) = x := by
  unfold seedSphereToCoord seedSphereFromCoord
  rw [(extChartAt (𝓡 4) seedPoint).right_inv (by rw [centeredSphereChart_target]; trivial)]
  exact seedCoordEquiv.symm_apply_apply x

lemma seedSphereFromCoord_to {p : Base} (hp : p ∈ (extChartAt (𝓡 4) seedPoint).source) :
    seedSphereFromCoord (seedSphereToCoord p) = p := by
  unfold seedSphereToCoord seedSphereFromCoord
  rw [seedCoordEquiv.apply_symm_apply,(extChartAt (𝓡 4) seedPoint).left_inv hp]

theorem seed_chart_scalar_extension (v : Yau.Jets.Coord → ℝ) (hv : ContDiff ℝ ∞ v)
    (hc : HasCompactSupport v) :
    ∃ F : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ F ∧
      tsupport F ⊆ seedSphereFromCoord '' tsupport v ∧
      ∀ x, F (seedSphereFromCoord x) = v x := by
  let K := seedSphereFromCoord '' tsupport v
  have hK : IsCompact K := hc.image seedSphereFromCoord_continuous
  have hKU : K ⊆ (extChartAt (𝓡 4) seedPoint).source := by
    rintro p ⟨x,hx,rfl⟩
    exact seedSphereFromCoord_source x
  have hU : IsOpen (extChartAt (𝓡 4) seedPoint).source := isOpen_extChartAt_source seedPoint
  obtain ⟨b,hb,hbc,hbs,hbr,hb1⟩ := manifold_compact_smooth_cutoff (I := 𝓡 4) hK hU hKU
  let F : Base → ℝ := fun p ↦ b p*v (seedSphereToCoord p)
  have hF : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ F := by
    intro p
    by_cases hp : p ∈ tsupport b
    · have hcoord : ContMDiffAt (𝓡 4) 𝓘(ℝ,Yau.Jets.Coord) ∞ seedSphereToCoord p :=
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
    have hvne : v (seedSphereToCoord p) ≠ 0 := fun h ↦ hp (by simp [F,h])
    exact ⟨seedSphereToCoord p,subset_closure hvne,
      seedSphereFromCoord_to (hbs (subset_closure hbne))⟩
  refine ⟨F,hF,hs,?_⟩
  intro x
  dsimp [F]
  rw [seedSphereToCoord_from]
  by_cases hx : v x = 0
  · simp [hx]
  · have h := (hb1 (seedSphereFromCoord x) ⟨x,subset_closure hx,rfl⟩).eq_of_nhds
    rw [h,one_mul]

theorem seed_plus_compact_sphere_field (v : Yau.Jets.Coord → ℝ)
    (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v) (n : ℕ) :
    ∃ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u ∧
      tsupport (u-sphericalSeed n) ⊆ seedSphereFromCoord '' tsupport v ∧
      ∀ x, u (seedSphereFromCoord x) = seedCoordinateField n x+v x := by
  obtain ⟨F,hF,hFs,hval⟩ := seed_chart_scalar_extension v hv hc
  refine ⟨sphericalSeed n+F,(sphericalSeed_smooth n).add hF,?_,?_⟩
  · simpa using hFs
  · intro x
    change sphericalSeed n (seedSphereFromCoord x)+F (seedSphereFromCoord x) = _
    rw [hval]
    rfl

end
end Yau.Target

end OAI
