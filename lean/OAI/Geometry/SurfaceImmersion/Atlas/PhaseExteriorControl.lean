import OAI.Geometry.SurfaceImmersion.Primitive.PhaseProfileStability
import OAI.Geometry.SurfaceImmersion.Geometry.SecondFormNormalFields
import OAI.Geometry.SurfaceImmersion.Primitive.PhaseBoundaryProfile
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialSupport
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasLeadingProfileStability
import OAI.Geometry.SurfaceImmersion.Geometry.MetricGaussInvariance

namespace OAI

/-! Exterior C2 control in the actual nonlinear phase chart, including
the closure of the exterior where its boundary is glued. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates GeometryPreservation SurfaceVelocityFamily.Loop
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma phaseRealChartMap_eventuallyEq (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {F G : M → Space} {p : JetPolynomial.Base}
    (hp : T p ∈ (chart (i : M)).target)
    (hFG : F =ᶠ[𝓝 ((chart (i : M)).symm (T p))] G) :
    A.phaseRealChartMap i T F =ᶠ[𝓝 (baseEquiv p)] A.phaseRealChartMap i T G := by
  have hsource := (chart (i : M)).map_target hp
  have hz : F-G =ᶠ[𝓝 ((chart (i : M)).symm (T p))] 0 := by
    filter_upwards [hFG] with q hq
    simp only [Pi.sub_apply,hq,sub_self,Pi.zero_apply]
  have he := A.jetChartMap_eventually_zero i hsource hz
  rw [(chart (i : M)).right_inv hp] at he
  rw [A.jetChartMap_sub] at he
  have hg : A.jetChartMap i F =ᶠ[𝓝 (T p)] A.jetChartMap i G := by
    filter_upwards [he] with q hq
    exact sub_eq_zero.mp hq
  have ht := hT.continuous.tendsto p
  have hb := baseEquiv.symm.continuous.tendsto (baseEquiv p)
  rw [baseEquiv.symm_apply_apply] at hb
  exact hg.comp_tendsto (ht.comp hb)


lemma phase_profile_eq_on_exterior_closure (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {F G : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hG : ContMDiff planeModel spaceModel ∞ G) {O : Set JetPolynomial.Base}
    (hO : ∀ p ∈ O, T p ∈ (chart (i : M)).target)
    (hext : ∀ p ∈ O, F =ᶠ[𝓝 ((chart (i : M)).symm (T p))] G)
    (z : ℝ) :
    ∀ p ∈ closure O, realBoundaryProfile (A.phaseRealChartMap i T F) z (baseEquiv p) =
      realBoundaryProfile (A.phaseRealChartMap i T G) z (baseEquiv p) := by
  have he : EqOn (fun p => realBoundaryProfile (A.phaseRealChartMap i T F) z (baseEquiv p))
      (fun p => realBoundaryProfile (A.phaseRealChartMap i T G) z (baseEquiv p)) O := by
    intro p hp
    have hh := A.phaseRealChartMap_eventuallyEq i hT (hO p hp) (hext p hp)
    have hd (v : SmallModes.Base) := RealModes.coordDeriv_germ hh v
    have hdd (v w : SmallModes.Base) := RealModes.coordDeriv_germ (hd w) v
    funext j
    fin_cases j
    · exact (hd SmallModes.dx).eq_of_nhds
    · exact (hd SmallModes.dy).eq_of_nhds
    · exact (hdd SmallModes.dy SmallModes.dy).eq_of_nhds
    · exact (hdd SmallModes.dx SmallModes.dy).eq_of_nhds
    · exact congrArg (fun v => z • v) (hdd SmallModes.dx SmallModes.dx).eq_of_nhds
  exact he.closure ((realBoundaryProfile_smooth (A.phaseRealChartMap_smooth i hT hF) z).continuous.comp
    baseEquiv.continuous) ((realBoundaryProfile_smooth (A.phaseRealChartMap_smooth i hT hG) z).continuous.comp
    baseEquiv.continuous)

lemma phase_real_profile_correction_bound (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {S : Set JetPolynomial.Base} (hS : IsOpen S) (hSc : IsCompact (closure S)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F G : M → Space,
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
      ∀ C z : ℝ, 0 ≤ C → 0 ≤ z → z ≤ 1 → A.WeightedBound 1 2 C (G-F) → ∀ p ∈ S,
      ‖realBoundaryProfile (A.phaseRealChartMap i T G) z (baseEquiv p)-
        realBoundaryProfile (A.phaseRealChartMap i T F) z (baseEquiv p)‖ ≤ D*C := by
  obtain ⟨D,hD,hbound⟩ := A.phase_profile_correction_bound i hT hS hSc
  refine ⟨‖boundaryProfileMap‖*D,mul_nonneg (norm_nonneg _) hD,?_⟩
  intro F G hF hG C z hC hz hz1 hb p hp
  rw [← A.phaseRealChartMap_profile i hT hG,← A.phaseRealChartMap_profile i hT hF,← map_sub]
  exact (boundaryProfileMap.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (hbound F G hF hG C z hC hz hz1 hb p hp)
      (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

theorem phase_exterior_profile_bound_closure (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {S : Set JetPolynomial.Base} (hS : IsOpen S) (hSc : IsCompact (closure S)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel spaceModel ∞ V → ContMDiff planeModel spaceModel ∞ W →
      ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ O : Set JetPolynomial.Base, (∀ p ∈ O, T p ∈ (chart (i : M)).target) →
      (∀ p ∈ O, V =ᶠ[𝓝 ((chart (i : M)).symm (T p))] G) →
      ∀ p ∈ closure O ∩ S,
      ‖realBoundaryProfile (A.phaseRealChartMap i T W) 1 (baseEquiv p)-
        realBoundaryProfile (A.phaseRealChartMap i T F) 1 (baseEquiv p)‖ ≤ D*(b+c) := by
  obtain ⟨D,hD,hbound⟩ := A.phase_real_profile_correction_bound i hT hS hSc
  refine ⟨D,hD,?_⟩
  intro F G V W hF hG hV hW b c hb hc hGF hWV O hO hext p hp
  have he := A.phase_profile_eq_on_exterior_closure i hT hV hG hO hext 1 p hp.1
  have hfirst := hbound V W hV hW c 1 hc zero_le_one le_rfl hWV p hp.2
  have hsecond := hbound F G hF hG b 1 hb zero_le_one le_rfl hGF p hp.2
  have ht := norm_sub_le_norm_sub_add_norm_sub (realBoundaryProfile (A.phaseRealChartMap i T W) 1 (baseEquiv p))
    (realBoundaryProfile (A.phaseRealChartMap i T V) 1 (baseEquiv p))
    (realBoundaryProfile (A.phaseRealChartMap i T F) 1 (baseEquiv p))
  rw [he] at ht hfirst
  exact ht.trans ((add_le_add hfirst hsecond).trans_eq (by ring))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
