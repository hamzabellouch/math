import OAI.Geometry.SurfaceImmersion.Geometry.ProjectedNormalLocal
import OAI.Geometry.Immersion.ClosedSurface.AtlasPartition

namespace OAI

/-! One tolerance controls normal projection through every chart of the finite atlas. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma compact_chart_projection_stability (i : A.centers) {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hn : ContMDiff planeModel spaceModel ∞ n)
    (hunit : ∀ p, ‖n p‖ = 1)
    (hN : ∀ p v, inner ℝ (surfaceDifferential F p v) (n p) = 0)
    (hD : ∀ p ∈ tsupport (A.weight i),
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)))
      (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ G : M → Space, ∀ p ∈ tsupport (A.weight i),
      ‖coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i G)
        (planeCoordinateIsometry (chart (i : M) p))-
        coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))‖ < δ →
      ‖coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i G)
        (planeCoordinateIsometry (chart (i : M) p))-
        coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))‖ < δ →
      ‖A.chartProjectedNormal i G n p-n p‖ < ε := by
  let S := {p : M // p ∈ tsupport (A.weight i)}
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isClosed_tsupport (A.weight i)).isCompact
  let c : S → SmallModes.Base := fun p => planeCoordinateIsometry (chart (i : M) p.1)
  have hc : Continuous c := planeCoordinateIsometry.continuous.comp
    (((chart (i : M)).continuousOn.mono (A.weight_support i)).domRestrict)
  have hread := spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)
  have hX := (contDiff_real_coordDeriv hread dx).continuous.comp hc
  have hY := (contDiff_real_coordDeriv hread dy).continuous.comp hc
  have hnn : Continuous (fun p : S => spaceCoordinates (n p.1)) :=
    spaceCoordinates.continuous.comp (hn.continuous.comp continuous_subtype_val)
  let L := ‖spaceCoordinates.symm.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  obtain ⟨δ,hδ,hnear⟩ := GeometryPreservation.compact_raw_normal_projection hX hY hnn
    (fun p => hD p.1 p.2) (fun p => by
      rw [spaceCoordinates_dot,real_inner_self_eq_norm_sq,hunit]; norm_num)
    (fun p => A.vectorPlaneRead_normal i hF n hN p.2 dx)
    (fun p => A.vectorPlaneRead_normal i hF n hN p.2 dy) (div_pos hε (by positivity : 0 < L+1))
  refine ⟨δ,hδ,?_⟩
  intro G p hp hx hy
  have hh := (hnear ⟨p,hp⟩ _ _ hx hy).2
  let r := realNormalPart
    (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i G) (c ⟨p,hp⟩))
    (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i G) (c ⟨p,hp⟩))
    (spaceCoordinates (n p))-spaceCoordinates (n p)
  change ‖r‖ < ε/(L+1) at hh
  have he : A.chartProjectedNormal i G n p-n p = spaceCoordinates.symm r := by
    simp only [r,chartProjectedNormal,map_sub,ContinuousLinearEquiv.symm_apply_apply,c]
  rw [he]
  calc
    ‖spaceCoordinates.symm r‖ ≤ L*‖r‖ := spaceCoordinates.symm.toContinuousLinearMap.le_opNorm r
    _ ≤ (L+1)*‖r‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (L+1)*(ε/(L+1)) := mul_lt_mul_of_pos_left hh (by positivity)
    _ = ε := mul_div_cancel₀ _ (by positivity)

theorem compact_atlas_projection_stability {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hn : ContMDiff planeModel spaceModel ∞ n)
    (hunit : ∀ p, ‖n p‖ = 1)
    (hN : ∀ p v, inner ℝ (surfaceDifferential F p v) (n p) = 0)
    (hD : ∀ i p, p ∈ tsupport (A.weight i) →
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)))
      (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ G : M → Space, ∀ p : M,
      (∀ i : A.centers, A.weight i p ≠ 0 → ∀ v ∈ ({dx,dy} : Set SmallModes.Base),
        ‖coordDeriv v (spaceCoordinates ∘ A.vectorPlaneRead i G)
          (planeCoordinateIsometry (chart (i : M) p))-
          coordDeriv v (spaceCoordinates ∘ A.vectorPlaneRead i F)
          (planeCoordinateIsometry (chart (i : M) p))‖ < δ) →
      A.projectedNormalField G n p ≠ 0 ∧
        ‖A.unitProjectedNormalField G n p-n p‖ < ε := by
  classical
  let η := min (1/2 : ℝ) (ε/3)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hi := fun i => A.compact_chart_projection_stability i hF hn hunit hN (hD i) hη
  choose d hd hnear using hi
  obtain ⟨δ,hδ,_,hle⟩ := finite_positive_threshold d hd
  refine ⟨δ,hδ,?_⟩
  intro G p hp
  have hh := A.unitProjectedNormalField_sub_bound (F := G) (p := p) (hunit p)
    (lt_of_le_of_lt (min_le_left _ _) (by norm_num : (1/2:ℝ)<1)) (fun i hz =>
      (hnear i G p (subset_tsupport _ hz)
        ((hp i hz dx (by simp)).trans_le (hle i))
        ((hp i hz dy (by simp)).trans_le (hle i))).le)
  exact ⟨hh.1,hh.2.trans_lt (by have := min_le_right (1/2:ℝ) (ε/3); dsimp [η] at *; linarith)⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
