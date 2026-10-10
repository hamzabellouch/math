import OAI.Geometry.SurfaceImmersion.Primitive.IndependentCircularBoundary
import OAI.Geometry.SurfaceImmersion.Primitive.ExactCircularBoundary
import OAI.Geometry.SurfaceImmersion.Primitive.AnalyticCurveCrossingLoop
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricPositive
import OAI.Geometry.SurfaceImmersion.Primitive.ExactCircularPrimitive
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricRegularity
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricRead
import OAI.Geometry.SurfaceImmersion.Primitive.PhaseCircularPeriod
import OAI.Geometry.SurfaceImmersion.Primitive.ExactPhaseOriginalProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.PhaseLeadingProfileStability
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveProfileStability
import OAI.Geometry.SurfaceImmersion.Geometry.ExactGeometricFastFamily
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveMetric
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricJetMargins

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
local instance independent_constructedCircularBoundaryFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independent_constructedCircularBoundaryFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independent_constructedCircularBoundaryDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance independent_constructedCircularBoundaryDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance independent_constructedCircularBoundarySectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independent_constructedCircularBoundarySectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
open SurfaceJetCoordinates SurfaceVelocityFamily VelocityFrame
variable {g : SmoothMetric M} {F : M → Space}

theorem independent_constructed_circular_primitive_boundary [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : A₀.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {n : SmallModes.Base → NormalFrame.Vec} {T U : Set SmallModes.Base}
    (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ (A₀.phaseRealChartMap i e.symm F) p))
    (hN : ∀ p ∈ U, SmallModes.coordDeriv SmallModes.dx (A₀.phaseRealChartMap i e.symm F) p ⬝ᵥ n p = 0 ∧
      SmallModes.coordDeriv SmallModes.dy (A₀.phaseRealChartMap i e.symm F) p ⬝ᵥ n p = 0 ∧ n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < PhaseGeometry.coordinateMetricHessian
      (RealModes.inducedCoordinateMetric (A₀.phaseRealChartMap i e.symm F)) Prod.fst p SmallModes.dy SmallModes.dy)
    (haT : ∀ p ∈ T, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 →
      realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy p ≠ 0 ∧
      normalize (realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy p) ≠ -n p)
    {ι : Type*} [Finite ι] {Curves : ι → Set SmallModes.Base}
    (hCurves : ∀ j, IsCompact (Curves j)) (hCurvesT : ∀ j, Curves j ⊆ T)
    {P : Set SmallModes.Base} (hP : P.Finite)
    (hlocal : ∀ p ∈ (⋃ j, Curves j) \ P, ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧
        (∀ x ∈ (⋃ j, Curves j) ∩ N, f x = 0) ∧ fderiv ℝ f p (0,1) ≠ 0)
    {E : Set SmallModes.Base} (hE : E.Finite) (hET : E ⊆ T) (haE : ∀ x ∈ E, 0 < a x)
    (slopeBound : ℝ) (hSlope : 0 ≤ slopeBound)
    {b c k : ι → SmallModes.Base → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (hc : ∀ j, ContDiff ℝ ∞ (c j))
    (hk : ∀ j, ContDiff ℝ ∞ (k j))
    (hbc : ∀ j, ∀ x ∈ Curves j, b j x ≠ 0 ∨ c j x ≠ 0)
    (B : ℝ) (hB : 0 ≤ B) (hkb : ∀ j, ∀ x ∈ Curves j, -B ≤ k j x)
    (hold : ∀ j, ∀ x ∈ Curves j, a x = 0 →
      0 < ((SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dx
        (A₀.phaseRealChartMap i e.symm F)) x ⬝ᵥ
        normalize (realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy x))*b j x +
        Real.sqrt (realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy x ⬝ᵥ
          realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy x)*c j x)^2 + k j x*(b j x)^2)
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
    (hST : baseEquiv '' closure (S : Set JetPolynomial.Base) ⊆ T)
    (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
    (hKA : e.symm '' K ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base))
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (haoff : ∀ p ∉ K, a (baseEquiv p) = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + A₀.bundleRestore A₀.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {C : Set JetPolynomial.Base} (hC : IsCompact C)
    (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target)
    (hCurveC : ∀ j x, x ∈ Curves j → baseEquiv.symm x ∈ C)
    (hactive : ∀ j x, x ∈ Curves j → A₀.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0)
    (hcurv : ∀ j x, x ∈ Curves j → k j x ≤
      RealModes.coordinateGauss (fun y => A₀.phaseMetricRead i e.symm h y 0)
        (fun y => A₀.phaseMetricRead i e.symm h y 1)
        (fun y => A₀.phaseMetricRead i e.symm h y 2) x)
    (hEC : ∀ x ∈ E, baseEquiv.symm x ∈ C)
    (hactiveE : ∀ x ∈ E, A₀.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0)
    (hcurvE : ∀ x ∈ E, -B ≤ RealModes.coordinateGauss
      (fun y => A₀.phaseMetricRead i e.symm h y 0)
      (fun y => A₀.phaseMetricRead i e.symm h y 1)
      (fun y => A₀.phaseMetricRead i e.symm h y 2) x) :
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      (∀ p ∈ C, realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z (baseEquiv p) ∈
        regularBoundaryProfiles) ∧
      (∀ j x, x ∈ Curves j →
        RealModes.realSecondForm (A₀.phaseRealChartMap i e.symm W) (b j x,c j x) (b j x,c j x) x ≠ 0 ∧
        VelocityFrame.normalize (RealModes.realSecondForm (A₀.phaseRealChartMap i e.symm W)
          (b j x,c j x) (b j x,c j x) x) ≠
          -profilePreferred (realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z x)) ∧
      (∀ x ∈ E, ∀ r s : ℝ, |r| ≤ slopeBound → |s| ≤ slopeBound →
        let H := A₀.phaseRealChartMap i e.symm W
        let κ := RealModes.coordinateGaussianCurvature
          (RealModes.realMetric H SmallModes.dx SmallModes.dx)
          (RealModes.realMetric H SmallModes.dx SmallModes.dy)
          (RealModes.realMetric H SmallModes.dy SmallModes.dy) x
        0 < orderedCrossing H (1,r) (1,s) x κ ∧ 0 < orderedCrossing H (1,s) (1,r) x κ ∧
        ((0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ profilePreferred (realBoundaryProfile H z x) ∧
          0 < RealModes.realSecondForm H (1,s) (1,s) x ⬝ᵥ profilePreferred (realBoundaryProfile H z x)) ∨
         (0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ RealModes.realSecondForm H (1,s) (1,s) x ∧
          ∃ w : NormalFrame.Vec, profilePreferred (realBoundaryProfile H z x) ⬝ᵥ w = 0 ∧
            0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ w ∧
            0 < RealModes.realSecondForm H (1,s) (1,s) x ⬝ᵥ w))) ∧
      ∃ G : M → Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
        A₀.WeightedBound 1 3 ε (G-F) ∧
        ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
          A₀.WeightedBound 1 2 (z^8) (W-V) ∧
          (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
        ∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by
  have hFr := A₀.phaseRealChartMap_smooth i hi hF
  obtain ⟨Z,hTZ,hZU,O,hOZ,l,hQc,hQO,hamp,hzero,e₁,e₂,α,h₁,h₂,hα,hper,hvel,hreg,η,hη,havoid,hcross⟩ :=
    actual_analytic_curve_crossing_loop hFr ha hT hU hTU hn hI hN hHess haT hboundary
      hCurves hCurvesT hP hlocal hE hET haE slopeBound hSlope hb hc hk hbc B hB hkb hold
  let Q := lowJet (A₀.jetChartMap i F ∘ e.symm) '' closure (S : Set JetPolynomial.Base)
  have heq : A₀.phaseRealChartMap i e.symm F ∘ baseEquiv = A₀.jetChartMap i F ∘ e.symm :=
    A₀.phaseRealChartMap_comp_base i e.symm F
  have hQT : Q ⊆ lowJet (A₀.phaseRealChartMap i e.symm F ∘ baseEquiv) '' (baseEquiv ⁻¹' T) := by
    rintro _ ⟨p,hp,rfl⟩
    rw [heq]
    exact mem_image_of_mem _ (hST (mem_image_of_mem _ hp))
  have hQ : IsCompact Q := hSc.image (lowJet_smooth ((A₀.jetChartMap_smooth i hF).comp hi)).continuous
  have hFQ : MapsTo (lowJet (A₀.jetChartMap i F ∘ e.symm)) S Q :=
    fun p hp => mem_image_of_mem _ (subset_closure hp)
  have hv : ∀ J ∈ O, lowJetPosition J ∉ K → ∀ t, l.velocity (J,t) = normal J := by
    intro J hJ hp
    exact hzero J hJ (haoff _ hp)
  have hdetE (x : SmallModes.Base) (hx : x ∈ E) :
      A₀.phaseMetricRead i e.symm h x 0 * A₀.phaseMetricRead i e.symm h x 2 -
        (A₀.phaseMetricRead i e.symm h x 1)^2 ≠ 0 := by
    have hh := (A₀.phaseMetricRead_positive i h e he hi (hCS (hEC x hx)).2 (hactiveE x hx)).2
    rw [baseEquiv.apply_symm_apply] at hh
    exact ne_of_gt hh
  exact data.independent_exact_circular_primitive_boundary A₀ houter hF hmetric i e he hi hχ hχc hχs hcover
    l ha hamp hOZ h₁ h₂ hα (fun J hJ t => hvel J t) S hSc hTS hQ
    (hQT.trans hQO) hFQ K hK hKS hKA hone hv ℓ hℓx hℓy h htarget hC hCS
    hCurveC hactive hcurv η hη havoid hEC hactiveE hdetE B slopeBound hcurvE hcross
    (fun p hp t _ => hreg _ (hST (mem_image_of_mem _ (subset_closure (hCS hp).1))) t)

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
