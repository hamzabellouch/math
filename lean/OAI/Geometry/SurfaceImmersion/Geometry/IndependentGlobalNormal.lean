import OAI.Geometry.SurfaceImmersion.Geometry.IndependentGeometricNormal
import OAI.Geometry.SurfaceImmersion.Primitive.GeometricCircularNormal
import OAI.Geometry.SurfaceImmersion.Geometry.GeometricNormalExtension
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
local instance independent_globalCircularNormalFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independent_globalCircularNormalFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independent_globalCircularNormalDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance independent_globalCircularNormalDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance independent_globalCircularNormalSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independent_globalCircularNormalSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
open SurfaceJetCoordinates SurfaceVelocityFamily VelocityFrame
variable {g : SmoothMetric M} {F : M → Space}

theorem independent_global_circular_primitive_normal [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
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
    (ha0 : ∀ p, 0 ≤ a p)
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
    {b c : ι → SmallModes.Base → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (hc : ∀ j, ContDiff ℝ ∞ (c j))
    (hbc : ∀ j, ∀ x ∈ Curves j, b j x ≠ 0 ∨ c j x ≠ 0)
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
    (hactiveC : ∀ p ∈ C, A₀.chartWeight i (e.symm p) ≠ 0)
    (hEC : ∀ x ∈ E, baseEquiv.symm x ∈ C)
    (hold : ∀ j, ∀ x ∈ Curves j, a x = 0 →
      let H := A₀.phaseRealChartMap i e.symm F
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
      |c (right j) (x j)/b (right j) (x j)| ≤ slopeBound)    (B : SmoothingAtlas M) (curves : ι → PhaseBoundaryCurve B)
    (n₀ : PreferredNormal F)
    (hglobal : ∀ j p, p ∈ (curves j).carrier → (curves j).second F p ≠ 0 ∧
      spaceCoordinates (n₀.vector p) ≠ -normalize ((curves j).second F p))
    {D : Set M} (hD : IsOpen D) (hDr : interior (closure D) = D)
    (hDs : closure D ⊆ (chart (i : M)).source)
    (hDe : MapsTo (chart (i : M)) (closure D) e.source)
    (hDw : ∀ p ∈ closure D, A₀.weight i p ≠ 0)
    (E₀ : Set M) (hE₀ : E₀.Finite) (hE₀f : Disjoint E₀ (frontier D))
    (hsupport : A₀.phaseSurfaceSupport i e K = closure D)
    (hDC : ∀ p ∈ closure D, e (chart (i : M) p) ∈ C)
    (hcurveChart : ∀ j p, p ∈ (curves j).carrier → p ∈ closure D →
      baseEquiv (e (chart (i : M) p)) ∈ Curves j)
    (hvector : ∀ j p, p ∈ (curves j).carrier → p ∈ closure D →
      (b j (baseEquiv (e (chart (i : M) p))),c j (baseEquiv (e (chart (i : M) p)))) =
        fderiv ℝ (surfacePhaseTransition ((curves j).index : M) (curves j).phase (i : M) e)
          ((curves j).coordinate p) SmallModes.dy)
    (hworldBoundary : ∀ p ∈ frontier D,
      realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy
        (baseEquiv (e (chart (i : M) p))) ≠ 0 ∧
      spaceCoordinates (n₀.vector p) ≠ -normalize (realSecondForm (A₀.phaseRealChartMap i e.symm F)
        SmallModes.dy SmallModes.dy (baseEquiv (e (chart (i : M) p)))))
    (haFrontier : ∀ p ∈ frontier D, a (baseEquiv (e (chart (i : M) p))) = 0)
    (hpositive : ∀ j p, p ∈ (curves j).carrier → p ∈ frontier D →
      0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n₀.vector p))
    (hVfrontier : ∀ p ∈ frontier D, baseEquiv (e (chart (i : M) p)) ∉ V)
    (hσD : ∀ j, (surfacePhaseChart (i : M) e).symm (x j) ∈ E₀ ∩ D) :
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      ∃ N : PreferredNormal W,
        (∀ j p, p ∈ (curves j).carrier → (curves j).second W p ≠ 0 ∧
          spaceCoordinates (N.vector p) ≠ -normalize ((curves j).second W p)) ∧
        (∀ p ∈ E₀, p ∉ D → N.vector p = A₀.unitProjectedNormalField W n₀.vector p) ∧
        (∀ j,
          let H := A₀.phaseRealChartMap i e.symm W
          let κ := coordinateGaussianCurvature (realMetric H SmallModes.dx SmallModes.dx)
            (realMetric H SmallModes.dx SmallModes.dy) (realMetric H SmallModes.dy SmallModes.dy) (x j)
          let p := (surfacePhaseChart (i : M) e).symm (x j)
          0 < orderedCrossing H (b (left j) (x j),c (left j) (x j))
            (b (right j) (x j),c (right j) (x j)) (x j) κ ∧
          0 < orderedCrossing H (b (right j) (x j),c (right j) (x j))
            (b (left j) (x j),c (left j) (x j)) (x j) κ ∧
          0 < realSecondForm H (b (left j) (x j),c (left j) (x j))
            (b (left j) (x j),c (left j) (x j)) (x j) ⬝ᵥ spaceCoordinates (N.vector p) ∧
          0 < realSecondForm H (b (right j) (x j),c (right j) (x j))
            (b (right j) (x j),c (right j) (x j)) (x j) ⬝ᵥ spaceCoordinates (N.vector p)) ∧
      ∃ G : M → Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
        A₀.WeightedBound 1 3 ε (G-F) ∧
        ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
          A₀.WeightedBound 1 2 (z^8) (W-V) ∧
          (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
          ∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hFiso : IsSmoothIsometricImmersion M g F := ⟨hF,fun p v w => by rw [hmetric]; rfl⟩
  obtain ⟨ρ,hρ,hextend⟩ := A₀.geometric_normal_extension B hFiso n₀ houter
    curves hglobal i e he hi hD hDr hDs hDe hDw E₀ hE₀ hE₀f
    (fun j p => (b j p,c j p)) (fun j => (hb j).continuous.prodMk (hc j).continuous)
    hvector hworldBoundary hpositive (fun j p hp hpf =>
      hold j _ (hcurveChart j p hp (frontier_subset_closure hpf)) (haFrontier p hpf))
  intro ε hε ζ hζ
  let ε₀ := min ε (ρ/4)
  let ζ₀ := min ζ (ρ/4)
  have hε₀ : 0 < ε₀ := lt_min hε (by positivity)
  have hζ₀ : 0 < ζ₀ := lt_min hζ (by positivity)
  obtain ⟨z,hz,hzζ,hz1,W,hW,hdata,hreg,havoid,hcross,hlocal,hrest⟩ :=
    data.independent_geometric_circular_primitive_normal A₀ houter hF hmetric i e he hi hχ hχc hχs hcover
      ha hT hU hTU hn hI hN hHess ha0 hboundary hCurves hCurvesT hP hlocal
      hE hET haE slopeBound hSlope hb hc hbc S hSc hTS hST K hK hKS hKA hone haoff
      ℓ hℓx hℓy h htarget hC hCS hCurveC hactiveC hEC hold left right x hxinj hxE
      hV hxV honly hfirst hslopes ε₀ hε₀ ζ₀ hζ₀
  obtain ⟨U₀,hU₀,hCU₀,ν,hν,hunit,hnormal,hcanonical,hνavoid,hνcross⟩ := hlocal
  obtain ⟨G,hG,hGF,V₀,hV₀,hWV,hVouter,hVsupport⟩ := hrest
  have hsmall : ε₀+z^8 < ρ := by
    have hz8 : z^8 ≤ z := calc
      z^8 = z*z^7 := by ring
      _ ≤ z*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hz.le hz1) hz.le
      _ = z := mul_one _
    have heps : ε₀ ≤ ρ/4 := min_le_right _ _
    have hzz : z < ρ/4 := hzζ.trans_le (min_le_right _ _)
    linarith
  have hGF₂ : A₀.WeightedBound 1 2 ε₀ (G-F) := fun j => (hGF j).mono_order (by decide)
  obtain ⟨N,hNav,hNmatch⟩ := hextend G V₀ W hG hV₀ h hW ε₀ (z^8) hε₀.le
    (pow_nonneg hz.le _) hsmall hGF₂ hWV
    (fun p hp => hVsupport p (by rwa [hsupport])) z U₀ hU₀ ν hν hunit hnormal
    (fun p hp => hCU₀ ⟨e (chart (i : M) p),hDC p hp,rfl⟩)
    (fun p hp => hcanonical _ (hCU₀ ⟨e (chart (i : M) p),hDC p (frontier_subset_closure hp),rfl⟩)
      (hVfrontier p hp))
    (fun j p hp hpD => ⟨(havoid j _ (hcurveChart j p hp (subset_closure hpD))).1,
      hνavoid j _ (hcurveChart j p hp (subset_closure hpD))⟩)
  refine ⟨z,hz,hzζ.trans_le (min_le_left _ _),hz1,W,hW,hdata,N,hNav,
    (fun p hp hpD => (hNmatch p hp).2 hpD),?_,G,hG,?_,V₀,hV₀,hWV,hVouter,hVsupport⟩
  · intro j
    have hxT : x j ∈ (surfacePhaseChart (i : M) e).target := by
      constructor
      · change baseEquiv.symm (x j) ∈ e.target
        exact (hCS (hEC _ (hxE j))).2
      · change e.symm (baseEquiv.symm (x j)) ∈ (chart (i : M)).target
        have ha := hactiveC _ (hEC _ (hxE j))
        by_contra hh
        simp only [SmoothingAtlas.chartWeight,indicator_of_notMem hh] at ha
        exact ha rfl
    have heq : spaceCoordinates (N.vector ((surfacePhaseChart (i : M) e).symm (x j))) = ν (x j) := by
      rw [(hNmatch _ (hσD j).1).1 (hσD j).2,A₀.phaseNormalLift_coordinates]
      exact congrArg ν ((surfacePhaseChart (i : M) e).right_inv hxT)
    dsimp only
    rw [heq]
    exact hνcross j
  · exact fun j => (hGF j).mono_const (min_le_left _ _)

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
