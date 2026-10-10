import OAI.Geometry.SurfaceImmersion.Atlas.CrossAtlasBounds
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseExteriorControl
import OAI.Geometry.SurfaceImmersion.Geometry.ExteriorClosureNormal
import OAI.Geometry.SurfaceImmersion.Atlas.ImmersedAtlasNormal

namespace OAI

/-! Exterior control in a fixed curve chart, while the analytic construction
and projected normal use the current immersion's smoothing atlas. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes GeometryPreservation
variable {M X : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem cross_phase_exterior_control {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p)) (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : B.centers) {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {S : Set JetPolynomial.Base} (hS : IsOpen S) (hSc : IsCompact (closure S))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ (O : Set M) (P : Set JetPolynomial.Base),
      (∀ y ∈ P, T y ∈ (chart (i : M)).target) →
      (∀ y ∈ P, (chart (i : M)).symm (T y) ∈ O) →
      (∀ y ∈ O, V =ᶠ[𝓝 y] G) → ∀ p ∈ closure O, ∀ q ∈ closure P ∩ S,
      A.projectedNormalField W n.vector p ≠ 0 ∧
      ‖spaceCoordinates (A.unitProjectedNormalField W n.vector p)-spaceCoordinates (n.vector p)‖ < ε ∧
      ‖realBoundaryProfile (B.phaseRealChartMap i T W) 1 (baseEquiv q)-
        realBoundaryProfile (B.phaseRealChartMap i T F) 1 (baseEquiv q)‖ < ε := by
  obtain ⟨D,hD,hbound⟩ := B.phase_exterior_profile_bound_closure i hT hS hSc
  obtain ⟨E,hE,hchange⟩ := A.weightedBound_change_atlas (V := Space) B 2
  let L := ‖spaceCoordinates.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  have hLp : 0 < L+1 := by positivity
  obtain ⟨r,hr,hnorm⟩ := A.exterior_projected_normal_close_closure hF n.smooth n.unit n.normal
    (fun j y hy => A.planeRead_gram_of_immersion hF hI houter j hy) (div_pos hε hLp)
  have hDE : 0 ≤ D*E := mul_nonneg hD hE
  refine ⟨min r (ε/(D*E+1)),lt_min hr (div_pos hε (by positivity)),?_⟩
  intro G V W hG hV hW b c hb hc hbc hGF hWV O P hP hPO hext p hp q hq
  obtain ⟨hne,hnear⟩ := hnorm G V W hG hV hW b c hb hc
    (hbc.trans_le (min_le_left _ _)) hGF hWV O hext p hp
  have hprof := hbound F G V W hF hG hV hW (E*b) (E*c) (mul_nonneg hE hb) (mul_nonneg hE hc)
    (hchange (G-F) 1 b zero_lt_one le_rfl hb (hG.sub hF) hGF)
    (hchange (W-V) 1 c zero_lt_one le_rfl hc (hW.sub hV) hWV)
    P hP (fun y hy => hext _ (hPO y hy)) q hq
  have hsmall : D*(E*b+E*c) < ε := by
    have ht := (lt_div_iff₀ (by positivity : 0 < D*E+1)).mp
      (hbc.trans_le (min_le_right _ _))
    have hbc0 : 0 ≤ b+c := add_nonneg hb hc
    nlinarith
  refine ⟨hne,?_,hprof.trans_lt hsmall⟩
  rw [← map_sub]
  calc
    ‖spaceCoordinates (A.unitProjectedNormalField W n.vector p-n.vector p)‖ ≤
        L*‖A.unitProjectedNormalField W n.vector p-n.vector p‖ :=
      spaceCoordinates.toContinuousLinearMap.le_opNorm _
    _ ≤ (L+1)*‖A.unitProjectedNormalField W n.vector p-n.vector p‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (L+1)*(ε/(L+1)) := mul_lt_mul_of_pos_left hnear hLp
    _ = ε := mul_div_cancel₀ _ hLp.ne'

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
