import OAI.Geometry.SurfaceImmersion.Atlas.PhaseExteriorControl
import OAI.Geometry.SurfaceImmersion.Geometry.BoundaryNormalMatching
import OAI.Geometry.SurfaceImmersion.Geometry.ExteriorClosureNormal
import OAI.Geometry.SurfaceImmersion.Atlas.ImmersedAtlasNormal

namespace OAI

/-! Apply the boundary matching estimate to the exact primitive's exterior
comparison and its actual projected old normal. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes NormalFrame GeometryPreservation
variable {M X : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [TopologicalSpace X] [CompactSpace X]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem compact_phase_boundary_avoidance {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p)) (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : A.centers) {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {S : Set JetPolynomial.Base} (hS : IsOpen S) (hSc : IsCompact (closure S))
    {p : X → M} {q : X → JetPolynomial.Base} (hp : Continuous p) (hq : Continuous q)
    (O : Set M) (P : Set JetPolynomial.Base)
    (hP : ∀ y ∈ P, T y ∈ (chart (i : M)).target)
    (hPO : ∀ y ∈ P, (chart (i : M)).symm (T y) ∈ O)
    (hpO : ∀ x, p x ∈ closure O) (hqP : ∀ x, q x ∈ closure P ∩ S)
    (hD : ∀ x, NormalFrame.gramDet
      (coordDeriv dx (A.phaseRealChartMap i T F) (baseEquiv (q x)))
      (coordDeriv dy (A.phaseRealChartMap i T F) (baseEquiv (q x))) ≠ 0)
    (hB : ∀ x, realSecondForm (A.phaseRealChartMap i T F) dy dy (baseEquiv (q x)) ≠ 0)
    (havoid : ∀ x, spaceCoordinates (n.vector (p x)) ≠
      -VelocityFrame.normalize (realSecondForm (A.phaseRealChartMap i T F) dy dy (baseEquiv (q x))))
 :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      (∀ y ∈ O, V =ᶠ[𝓝 y] G) → ∀ x : X, ∀ z : ℝ,
      A.projectedNormalField W n.vector (p x) ≠ 0 ∧
      realSecondForm (A.phaseRealChartMap i T W) dy dy (baseEquiv (q x)) ≠ 0 ∧
      spaceCoordinates (A.unitProjectedNormalField W n.vector (p x)) ≠
        -profilePreferred (realBoundaryProfile (A.phaseRealChartMap i T W) z (baseEquiv (q x))) := by
  obtain ⟨δ,hδ,hmatch⟩ := compact_actual_exterior_avoidance
    (A.phaseRealChartMap_smooth i hT hF) (baseEquiv.continuous.comp hq)
    (spaceCoordinates.continuous.comp (n.smooth.continuous.comp hp))
    (v := fun _ => dy) continuous_const hD hB havoid
  obtain ⟨D,hD0,hprofile⟩ := A.phase_exterior_profile_bound_closure i hT hS hSc
  let L := ‖spaceCoordinates.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  have hLp : 0 < L+1 := by positivity
  obtain ⟨r,hr,hnorm⟩ := A.exterior_projected_normal_close_closure hF n.smooth n.unit n.normal
    (fun j y hy => A.planeRead_gram_of_immersion hF hI houter j hy) (div_pos hδ hLp)
  refine ⟨min r (δ/(D+1)),lt_min hr (div_pos hδ (by positivity)),?_⟩
  intro G V W hG hV hW b c hb hc hbc hGF hWV hext x z
  obtain ⟨hne,hnear⟩ := hnorm G V W hG hV hW b c hb hc
    (hbc.trans_le (min_le_left _ _)) hGF hWV O hext (p x) (hpO x)
  have hprof := hprofile F G V W hF hG hV hW b c hb hc hGF hWV P hP
    (fun y hy => hext _ (hPO y hy)) (q x) (hqP x)
  have hsmall : D*(b+c) < δ := by
    have ht := (lt_div_iff₀ (by positivity : 0 < D+1)).mp
      (hbc.trans_le (min_le_right _ _))
    nlinarith
  have hcoord : ‖spaceCoordinates (A.unitProjectedNormalField W n.vector (p x))-
      spaceCoordinates (n.vector (p x))‖ < δ := by
    rw [← map_sub]
    calc
      ‖spaceCoordinates (A.unitProjectedNormalField W n.vector (p x)-n.vector (p x))‖ ≤
          L*‖A.unitProjectedNormalField W n.vector (p x)-n.vector (p x)‖ :=
        spaceCoordinates.toContinuousLinearMap.le_opNorm _
      _ ≤ (L+1)*‖A.unitProjectedNormalField W n.vector (p x)-n.vector (p x)‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (L+1)*(δ/(L+1)) := mul_lt_mul_of_pos_left hnear hLp
      _ = δ := mul_div_cancel₀ _ hLp.ne'
  exact ⟨hne,hmatch x _ (A.phaseRealChartMap_smooth i hT hW) _ (hprof.trans_lt hsmall) hcoord⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
