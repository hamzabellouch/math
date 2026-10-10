import OAI.Geometry.SurfaceImmersion.Geometry.ExteriorClosureNormal
import OAI.Geometry.SurfaceImmersion.Atlas.ImmersedAtlasNormal
import OAI.Geometry.SurfaceImmersion.Primitive.ExteriorProfileBounds

namespace OAI

/-! A single smallness threshold controls the exterior second jet and
preferred normal together, uniformly over the fixed finite atlas. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exterior_jet_normal_control_closure {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p)) (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ O : Set M, (∀ q ∈ O, V =ᶠ[𝓝 q] G) →
      ∀ i : A.centers, ∀ p ∈ closure O, p ∈ tsupport (A.weight i) →
      ‖realBoundaryProfile (spaceCoordinates ∘ A.vectorPlaneRead i W) 1
        (planeCoordinateIsometry (chart (i : M) p))-
        realBoundaryProfile (spaceCoordinates ∘ A.vectorPlaneRead i F) 1
        (planeCoordinateIsometry (chart (i : M) p))‖ < ε ∧
      A.projectedNormalField W n.vector p ≠ 0 ∧
      ‖spaceCoordinates (A.unitProjectedNormalField W n.vector p)-spaceCoordinates (n.vector p)‖ < ε := by
  classical
  let L := ‖spaceCoordinates.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  have hLp : 0 < L+1 := by positivity
  obtain ⟨r,hr,hnclose⟩ := A.exterior_projected_normal_close_closure hF n.smooth n.unit n.normal
    (fun i p hp => A.planeRead_gram_of_immersion hF hI houter i hp)
    (div_pos hε hLp)
  choose D hD hprofile using fun i => A.exterior_profile_bound_closure i
  obtain ⟨s,hs,_,hsi⟩ := finite_positive_threshold (fun i => ε/(D i+1))
    (fun i => div_pos hε (by have := hD i; positivity))
  refine ⟨min r s,lt_min hr hs,?_⟩
  intro G V W hG hV hW b c hb hc hbc hGF hWV O hext i p hpO hp
  obtain ⟨hne,hnorm⟩ := hnclose G V W hG hV hW b c hb hc
    (hbc.trans_le (min_le_left _ _)) hGF hWV O hext p hpO
  have hprof := hprofile i F G V W hF hG hV hW b c hb hc hGF hWV O hext p hpO hp
  have hsmall : D i*(b+c) < ε := by
    have ht := (lt_div_iff₀ (by have := hD i; positivity : 0 < D i+1)).mp
      ((hbc.trans_le (min_le_right _ _)).trans_le (hsi i))
    nlinarith
  refine ⟨hprof.trans_lt hsmall,hne,?_⟩
  rw [← map_sub]
  calc
    ‖spaceCoordinates (A.unitProjectedNormalField W n.vector p-n.vector p)‖ ≤
        L*‖A.unitProjectedNormalField W n.vector p-n.vector p‖ :=
      spaceCoordinates.toContinuousLinearMap.le_opNorm _
    _ ≤ (L+1)*‖A.unitProjectedNormalField W n.vector p-n.vector p‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (L+1)*(ε/(L+1)) := mul_lt_mul_of_pos_left hnorm hLp
    _ = ε := mul_div_cancel₀ _ hLp.ne'

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
