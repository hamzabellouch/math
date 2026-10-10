import OAI.Geometry.SurfaceImmersion.Primitive.PreservingCircularNormal
import OAI.Geometry.SurfaceImmersion.Primitive.PhasePrimitiveBoundaryGauss
import OAI.Geometry.SurfaceImmersion.Geometry.CompactSlopeNormal
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseGaussRepresentative
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
local instance geometricCircularNormalFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance geometricCircularNormalFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance geometricCircularNormalDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance geometricCircularNormalDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance geometricCircularNormalSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance geometricCircularNormalSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
open SurfaceJetCoordinates SurfaceVelocityFamily VelocityFrame
variable {g : SmoothMetric M} {F : M → Space}

theorem geometric_circular_primitive_normal [T2Space M] (data : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : data.A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (data.A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {n : SmallModes.Base → NormalFrame.Vec} {T U : Set SmallModes.Base}
    (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ (data.A.phaseRealChartMap i e.symm F) p))
    (hN : ∀ p ∈ U, SmallModes.coordDeriv SmallModes.dx (data.A.phaseRealChartMap i e.symm F) p ⬝ᵥ n p = 0 ∧
      SmallModes.coordDeriv SmallModes.dy (data.A.phaseRealChartMap i e.symm F) p ⬝ᵥ n p = 0 ∧ n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < PhaseGeometry.coordinateMetricHessian
      (RealModes.inducedCoordinateMetric (data.A.phaseRealChartMap i e.symm F)) Prod.fst p SmallModes.dy SmallModes.dy)
    (ha0 : ∀ p, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 →
      realSecondForm (data.A.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy p ≠ 0 ∧
      normalize (realSecondForm (data.A.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy p) ≠ -n p)
    {ι : Type*} [Finite ι] {Curves : ι → Set SmallModes.Base}
    (hCurves : ∀ j, IsCompact (Curves j)) (hCurvesT : ∀ j, Curves j ⊆ T)
    {P : Set SmallModes.Base} (hP : P.Finite)
    (hlocal : ∀ p ∈ (⋃ j, Curves j) \ P, ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧
        (∀ x ∈ (⋃ j, Curves j) ∩ N, f x = 0) ∧ fderiv ℝ f p (0,1) ≠ 0)
    {E : Set SmallModes.Base} (hE : E.Finite) (hET : E ⊆ T) (haE : ∀ x ∈ E, 0 < a x)
    (slopeBound : ℝ) (hSlope : 0 ≤ slopeBound)
    {b c : ι → SmallModes.Base → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (hc : ∀ j, ContDiff ℝ ∞ (c j))
    (hbc : ∀ j, ∀ x ∈ Curves j, b j x ≠ 0 ∨ c j x ≠ 0)
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
    (hST : baseEquiv '' closure (S : Set JetPolynomial.Base) ⊆ T)
    (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
    (hKA : e.symm '' K ⊆ (data.A.chartWeightCompact i : Set JetPolynomial.Base))
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (haoff : ∀ p ∉ K, a (baseEquiv p) = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + data.A.bundleRestore data.A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {C : Set JetPolynomial.Base} (hC : IsCompact C)
    (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target)
    (hCurveC : ∀ j x, x ∈ Curves j → baseEquiv.symm x ∈ C)
    (hactiveC : ∀ p ∈ C, data.A.chartWeight i (e.symm p) ≠ 0)
    (hEC : ∀ x ∈ E, baseEquiv.symm x ∈ C)
    (hold : ∀ j, ∀ x ∈ Curves j, a x = 0 →
      let H := data.A.phaseRealChartMap i e.symm F
      let κ := coordinateGaussianCurvature (realMetric H SmallModes.dx SmallModes.dx)
        (realMetric H SmallModes.dx SmallModes.dy) (realMetric H SmallModes.dy SmallModes.dy) x
      0 < orderedCrossing H SmallModes.dy (b j x,c j x) x κ)

    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (left right : σ → ι) (x : σ → SmallModes.Base) (hxinj : Function.Injective x)
    (hxE : ∀ j, x j ∈ E)
    {V : Set SmallModes.Base} (hV : IsOpen V) (hxV : ∀ j, x j ∈ V)
    (honly : ∀ j k, x j ∈ Curves k → k = left j ∨ k = right j)
    (hfirst : ∀ j, b (left j) (x j) ≠ 0 ∧ b (right j) (x j) ≠ 0)
    (hslopes : ∀ j, |c (left j) (x j)/b (left j) (x j)| ≤ slopeBound ∧
      |c (right j) (x j)/b (right j) (x j)| ≤ slopeBound)
 :
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      (∀ p ∈ C, realBoundaryProfile (data.A.phaseRealChartMap i e.symm W) z (baseEquiv p) ∈
        regularBoundaryProfiles) ∧
      (∀ j x, x ∈ Curves j →
        RealModes.realSecondForm (data.A.phaseRealChartMap i e.symm W) (b j x,c j x) (b j x,c j x) x ≠ 0 ∧
        VelocityFrame.normalize (RealModes.realSecondForm (data.A.phaseRealChartMap i e.symm W)
          (b j x,c j x) (b j x,c j x) x) ≠
          -profilePreferred (realBoundaryProfile (data.A.phaseRealChartMap i e.symm W) z x)) ∧
      (∀ x ∈ E, ∀ r s : ℝ, |r| ≤ slopeBound → |s| ≤ slopeBound →
        let H := data.A.phaseRealChartMap i e.symm W
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
      (∃ U₀ : Set SmallModes.Base, IsOpen U₀ ∧ baseEquiv '' C ⊆ U₀ ∧
        ∃ ν : SmallModes.Base → NormalFrame.Vec, ContDiffOn ℝ ∞ ν U₀ ∧
          (∀ p ∈ U₀, ν p ⬝ᵥ ν p = 1) ∧
          (∀ p ∈ U₀, ∀ v : SmallModes.Base,
            SmallModes.coordDeriv v (data.A.phaseRealChartMap i e.symm W) p ⬝ᵥ ν p = 0) ∧
          (∀ p ∈ U₀, p ∉ V → ν p =
            profilePreferred (realBoundaryProfile (data.A.phaseRealChartMap i e.symm W) z p)) ∧
          (∀ j p, p ∈ Curves j → ν p ≠ -normalize
            (realSecondForm (data.A.phaseRealChartMap i e.symm W) (b j p,c j p) (b j p,c j p) p)) ∧
          ∀ j,
            let H := data.A.phaseRealChartMap i e.symm W
            let κ := coordinateGaussianCurvature (realMetric H SmallModes.dx SmallModes.dx)
              (realMetric H SmallModes.dx SmallModes.dy) (realMetric H SmallModes.dy SmallModes.dy) (x j)
            0 < orderedCrossing H (b (left j) (x j),c (left j) (x j))
              (b (right j) (x j),c (right j) (x j)) (x j) κ ∧
            0 < orderedCrossing H (b (right j) (x j),c (right j) (x j))
              (b (left j) (x j),c (left j) (x j)) (x j) κ ∧
            0 < realSecondForm H (b (left j) (x j),c (left j) (x j))
              (b (left j) (x j),c (left j) (x j)) (x j) ⬝ᵥ ν (x j) ∧
            0 < realSecondForm H (b (right j) (x j),c (right j) (x j))
              (b (right j) (x j),c (right j) (x j)) (x j) ⬝ᵥ ν (x j)) ∧
      ∃ G : M → Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
        data.A.WeightedBound 1 3 ε (G-F) ∧
        ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
          data.A.WeightedBound 1 2 (z^8) (W-V) ∧
          (∀ p ∉ tsupport (data.A.weight i), V =ᶠ[𝓝 p] G) ∧
        ∀ p ∉ data.A.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by
  have hFiso : IsSmoothIsometricImmersion M g F := ⟨hF,fun p v w => by rw [hmetric]; rfl⟩
  have hs : ∀ j, ∀ x ∈ Curves j, a x = 0 →
      0 < ((SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dx
        (data.A.phaseRealChartMap i e.symm F)) x ⬝ᵥ
        normalize (realSecondForm (data.A.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy x))*b j x +
        Real.sqrt (realSecondForm (data.A.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy x ⬝ᵥ
          realSecondForm (data.A.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy x)*c j x)^2 + (coordinateGauss (fun y => data.A.phaseMetricRead i e.symm h y 0)
        (fun y => data.A.phaseMetricRead i e.symm h y 1)
        (fun y => data.A.phaseMetricRead i e.symm h y 2) x)*(b j x)^2 := by
    intro j x hx hz
    have hcx := hCurveC j x hx
    have hd := RealModes.gramDet_ne_zero_of_injective _ (hI x (hTU (hCurvesT j hx)))
    rw [← data.A.phase_primitive_boundary_crossing i e he hi hFiso h hχ ha htarget
      (hCS hcx).2 (hactiveC _ hcx) hz (Filter.Eventually.of_forall ha0) hd
      (hboundary x (hCurvesT j hx) hz).1 (b j x) (c j x)]
    exact hold j x hx hz
  exact data.preserving_circular_primitive_normal hF hmetric i e he hi hχ hχc hχs hcover
    ha hT hU hTU hn hI hN hHess (fun p _ => ha0 p) hboundary hCurves hCurvesT hP hlocal
    hE hET haE slopeBound hSlope hb hc hbc S hSc hTS hST K hK hKS hKA hone haoff
    ℓ hℓx hℓy h htarget hC hCS hCurveC hactiveC hEC hs left right x hxinj hxE
    hV hxV honly hfirst hslopes

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
