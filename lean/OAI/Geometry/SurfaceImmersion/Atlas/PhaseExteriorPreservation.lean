import OAI.Geometry.SurfaceImmersion.Atlas.CrossPhaseExteriorControl
import OAI.Geometry.SurfaceImmersion.Primitive.IntrinsicExteriorCrossings
import OAI.Geometry.SurfaceImmersion.Geometry.BoundaryJetAvoidance

namespace OAI

/-! Actual later-curve geometry is stable in its own fixed phase chart,
even when the exact correction uses a different smoothing atlas. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes GeometryPreservation VelocityFrame
variable {M X : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [TopologicalSpace X] [CompactSpace X]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem compact_phase_exterior_curve_preservation {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p)) (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : B.centers) {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {S : Set JetPolynomial.Base} (hS : IsOpen S) (hSc : IsCompact (closure S))
    {p : X → M} {q : X → JetPolynomial.Base} (hp : Continuous p) (hq : Continuous q)
    {v : X → SmallModes.Base} (hv : Continuous v)
    (O : Set M) (P : Set JetPolynomial.Base)
    (hP : ∀ y ∈ P, T y ∈ (chart (i : M)).target)
    (hPO : ∀ y ∈ P, (chart (i : M)).symm (T y) ∈ O)
    (hpO : ∀ x, p x ∈ closure O) (hqP : ∀ x, q x ∈ closure P ∩ S)
    (hD : ∀ x, NormalFrame.gramDet
      (coordDeriv dx (B.phaseRealChartMap i T F) (baseEquiv (q x)))
      (coordDeriv dy (B.phaseRealChartMap i T F) (baseEquiv (q x))) ≠ 0)
    (hB : ∀ x, realSecondForm (B.phaseRealChartMap i T F) (v x) (v x) (baseEquiv (q x)) ≠ 0)
    (havoid : ∀ x, spaceCoordinates (n.vector (p x)) ≠
      -normalize (realSecondForm (B.phaseRealChartMap i T F) (v x) (v x) (baseEquiv (q x)))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      (∀ y ∈ O, V =ᶠ[𝓝 y] G) → ∀ x : X,
      A.projectedNormalField W n.vector (p x) ≠ 0 ∧
      realSecondForm (B.phaseRealChartMap i T W) (v x) (v x) (baseEquiv (q x)) ≠ 0 ∧
      spaceCoordinates (A.unitProjectedNormalField W n.vector (p x)) ≠
        -normalize (realSecondForm (B.phaseRealChartMap i T W) (v x) (v x) (baseEquiv (q x))) := by
  obtain ⟨δ,hδ,havoid'⟩ := compact_actual_exterior_avoidance (B.phaseRealChartMap_smooth i hT hF)
    (baseEquiv.continuous.comp hq) (spaceCoordinates.continuous.comp (n.smooth.continuous.comp hp))
    hv hD hB havoid
  obtain ⟨ρ,hρ,hcontrol⟩ := A.cross_phase_exterior_control B hF hI n houter i hT hS hSc hδ
  refine ⟨ρ,hρ,?_⟩
  intro G V W hG hV hW b c hb hc hbc hGF hWV hext x
  obtain ⟨hne,hn,hj⟩ := hcontrol G V W hG hV hW b c hb hc hbc hGF hWV O P hP hPO hext
    (p x) (hpO x) (q x) (hqP x)
  exact ⟨hne,havoid' x _ (B.phaseRealChartMap_smooth i hT hW) _ hj hn⟩


theorem compact_phase_exterior_crossing_preservation {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p)) (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : B.centers) {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {S : Set JetPolynomial.Base} (hS : IsOpen S) (hSc : IsCompact (closure S))
    {p : X → M} {q : X → JetPolynomial.Base} (hp : Continuous p) (hq : Continuous q)
    (O : Set M) (P : Set JetPolynomial.Base)
    (hP : ∀ y ∈ P, T y ∈ (chart (i : M)).target)
    (hPO : ∀ y ∈ P, (chart (i : M)).symm (T y) ∈ O)
    (hpO : ∀ x, p x ∈ closure O) (hqP : ∀ x, q x ∈ closure P ∩ S)
    (hD : ∀ x, NormalFrame.gramDet
      (coordDeriv dx (B.phaseRealChartMap i T F) (baseEquiv (q x)))
      (coordDeriv dy (B.phaseRealChartMap i T F) (baseEquiv (q x))) ≠ 0)
    {v w : X → SmallModes.Base} (hv : Continuous v) (hw : Continuous w)
    (hpositive : ∀ x,
      0 < realSecondForm (B.phaseRealChartMap i T F) (v x) (v x)
        (baseEquiv (q x)) ⬝ᵥ spaceCoordinates (n.vector (p x)) ∧
      0 < realSecondForm (B.phaseRealChartMap i T F) (w x) (w x)
        (baseEquiv (q x)) ⬝ᵥ spaceCoordinates (n.vector (p x)))
    (hcross : ∀ x,
      0 < orderedCrossing (B.phaseRealChartMap i T F) (v x) (w x)
        (baseEquiv (q x)) (coordinateGaussianCurvature (realMetric (B.phaseRealChartMap i T F) dx dx)
        (realMetric (B.phaseRealChartMap i T F) dx dy)
        (realMetric (B.phaseRealChartMap i T F) dy dy)
        (baseEquiv (q x))) ∧
      0 < orderedCrossing (B.phaseRealChartMap i T F) (w x) (v x)
        (baseEquiv (q x)) (coordinateGaussianCurvature (realMetric (B.phaseRealChartMap i T F) dx dx)
        (realMetric (B.phaseRealChartMap i T F) dx dy)
        (realMetric (B.phaseRealChartMap i T F) dy dy)
        (baseEquiv (q x)))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      (∀ y ∈ O, V =ᶠ[𝓝 y] G) →
      ∀ x : X,
      (0 < realSecondForm (B.phaseRealChartMap i T W) (v x) (v x)
        (baseEquiv (q x)) ⬝ᵥ
          spaceCoordinates (A.unitProjectedNormalField W n.vector (p x)) ∧
       0 < realSecondForm (B.phaseRealChartMap i T W) (w x) (w x)
        (baseEquiv (q x)) ⬝ᵥ
          spaceCoordinates (A.unitProjectedNormalField W n.vector (p x))) ∧
      (0 < orderedCrossing (B.phaseRealChartMap i T W) (v x) (w x)
        (baseEquiv (q x)) (coordinateGaussianCurvature (realMetric (B.phaseRealChartMap i T W) dx dx)
        (realMetric (B.phaseRealChartMap i T W) dx dy)
        (realMetric (B.phaseRealChartMap i T W) dy dy)
        (baseEquiv (q x))) ∧
       0 < orderedCrossing (B.phaseRealChartMap i T W) (w x) (v x)
        (baseEquiv (q x)) (coordinateGaussianCurvature (realMetric (B.phaseRealChartMap i T W) dx dx)
        (realMetric (B.phaseRealChartMap i T W) dx dy)
        (realMetric (B.phaseRealChartMap i T W) dy dy)
        (baseEquiv (q x)))) := by
  have hread := B.phaseRealChartMap_smooth i hT hF
  have hcoord := baseEquiv.continuous.comp hq
  have hn := spaceCoordinates.continuous.comp (n.smooth.continuous.comp hp)
  obtain ⟨δv,hδv,hvclose⟩ := compact_actual_exterior_pairing hread hcoord hn hv hD
    (fun x => (hpositive x).1)
  obtain ⟨δw,hδw,hwclose⟩ := compact_actual_exterior_pairing hread hcoord hn hw hD
    (fun x => (hpositive x).2)
  have hB (a : X → SmallModes.Base) (h : ∀ x, 0 < realSecondForm (B.phaseRealChartMap i T F)
      (a x) (a x) (baseEquiv (q x)) ⬝ᵥ spaceCoordinates (n.vector (p x))) :
      ∀ x, realSecondForm (B.phaseRealChartMap i T F) (a x) (a x)
        (baseEquiv (q x)) ≠ 0 := by
    intro x he
    have hx := h x
    rw [he,zero_dotProduct] at hx
    exact lt_irrefl 0 hx
  obtain ⟨δc,hδc,hcclose⟩ := compact_actual_intrinsic_crossings hread hcoord hv hw hD
    (hB v (fun x => (hpositive x).1)) (hB w (fun x => (hpositive x).2)) hcross
  let δ := min δv (min δw δc)
  have hδ : 0 < δ := lt_min hδv (lt_min hδw hδc)
  have hδv' : δ ≤ δv := min_le_left _ _
  have hδw' : δ ≤ δw := (min_le_right _ _).trans (min_le_left _ _)
  have hδc' : δ ≤ δc := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ρ,hρ,hcontrol⟩ := A.cross_phase_exterior_control B hF hI n houter i hT hS hSc hδ
  refine ⟨ρ,hρ,?_⟩
  intro G V W hG hV hW b c hb hc hbc hGF hWV hext x
  obtain ⟨_,hnorm,hjet⟩ := hcontrol G V W hG hV hW b c hb hc hbc hGF hWV O P hP hPO hext
    (p x) (hpO x) (q x) (hqP x)
  have hW' := B.phaseRealChartMap_smooth i hT hW
  exact ⟨⟨hvclose x _ hW' _ (hjet.trans_le hδv') (hnorm.trans_le hδv'),
    hwclose x _ hW' _ (hjet.trans_le hδw') (hnorm.trans_le hδw')⟩,
    hcclose x _ hW' (hjet.trans_le hδc')⟩


end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
