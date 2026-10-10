import OAI.Geometry.NodalSets.Elliptic.SeedLogExtension

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric
open scoped Topology
noncomputable section

def seedCoordPatch (r : ℝ) : Set Coord := seedCoordEquiv ⁻¹' ball (0 : BaseModel) r

def seedCoordCube (a : ℝ) : Set Coord := Icc (fun _ ↦ -a) (fun _ ↦ a)

lemma seedCoordPatch_open (r : ℝ) : IsOpen (seedCoordPatch r) :=
  isOpen_ball.preimage seedCoordEquiv.continuous

lemma seedCoordPatch_closure_subset (r : ℝ) :
    closure (seedCoordPatch r) ⊆ seedCoordEquiv ⁻¹' closedBall (0 : BaseModel) r :=
  closure_minimal (preimage_mono ball_subset_closedBall)
    (isClosed_closedBall.preimage seedCoordEquiv.continuous)

lemma seedCoordPatch_compactClosure (r : ℝ) : IsCompact (closure (seedCoordPatch r)) := by
  have hc : IsCompact (seedCoordEquiv ⁻¹' closedBall (0 : BaseModel) r) := by
    have he : seedCoordEquiv ⁻¹' closedBall (0 : BaseModel) r =
        seedCoordEquiv.symm '' closedBall (0 : BaseModel) r := by
      ext x
      constructor
      · intro hx
        exact ⟨seedCoordEquiv x,hx,seedCoordEquiv.symm_apply_apply x⟩
      · rintro ⟨y,hy,rfl⟩
        simpa using hy
    rw [he]
    exact (isCompact_closedBall _ _).image seedCoordEquiv.symm.continuous
  exact hc.of_isClosed_subset isClosed_closure (seedCoordPatch_closure_subset r)

lemma seedCoordCube_image {a : ℝ} {x : Coord} (hx : x ∈ seedCoordCube a) :
    seedCoordEquiv x ∈ seedCoordinateCube a := by
  intro i
  change |x i| ≤ a
  exact abs_le.mpr ⟨hx.1 i,hx.2 i⟩

lemma seedCoordCube_subset {a r : ℝ} (h : seedCoordinateCube a ⊆ ball (0 : BaseModel) r) :
    seedCoordCube a ⊆ seedCoordPatch r := fun _ hx ↦ h (seedCoordCube_image hx)

lemma seedCoordCube_Icc (a : ℝ) :
    Icc (fun _ : Fin 4 ↦ -a) (fun _ : Fin 4 ↦ -a+2*a) = seedCoordCube a := by
  congr 1
  funext i
  ring

end
end Yau.Target

end OAI
