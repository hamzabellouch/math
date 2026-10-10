import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveDomainWindow
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveOuterGeometry

namespace OAI

/-! The constructed support and geometric domain of one actual primitive.
Every field is data or a local identity needed by the analytic realization. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
local instance patchFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance patchFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance patchDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance patchDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance patchSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance patchSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

structure SupportedPrimitivePatch (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (F : M → Space) (amp phi : M → ℝ) (D : Set M) where
  phase_smooth : ContDiff ℝ ∞ e
  inverse_smooth : ContDiff ℝ ∞ e.symm
  outer : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1)
  cover : (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source
  cutoff : JetPolynomial.Base → ℝ
  cutoff_smooth : ContDiff ℝ ∞ cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_source : tsupport cutoff ⊆ e.source
  amplitude : SmallModes.Base → ℝ
  amplitude_smooth : ContDiff ℝ ∞ amplitude
  amplitude_nonneg : ∀ x, 0 ≤ amplitude x
  amplitude_surface : ∀ p ∈ (surfacePhaseChart (i : M) e).source,
    amplitude (surfacePhaseChart (i : M) e p) = amp p
  amplitude_positive : ∀ x, 0 < amplitude x ↔ x ∈ (surfacePhaseChart (i : M) e) '' D
  compactSet : Set JetPolynomial.Base
  compact : IsCompact compactSet
  target : compactSet ⊆ e.target
  support : A.phaseSurfaceSupport i e compactSet = closure D
  inverse_support : e.symm '' compactSet ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base)
  cutoff_one : ∀ x ∈ e.symm '' compactSet, cutoff x = 1
  amplitude_off : ∀ x ∉ compactSet, amplitude (baseEquiv x) = 0
  compact_active : ∀ x ∈ compactSet, A.chartWeight i (e.symm x) ≠ 0
  closed_coordinates : ∀ p ∈ closure D, e (chart (i : M) p) ∈ compactSet
  source_closed : closure D ⊆ (surfacePhaseChart (i : M) e).source
  active_closed : ∀ p ∈ closure D, A.weight i p ≠ 0
  window : TopologicalSpace.Opens JetPolynomial.Base
  window_compact : IsCompact (closure (window : Set JetPolynomial.Base))
  phase_window : MapsTo e e.source window
  support_window : compactSet ⊆ window
  region : Set SmallModes.Base
  region_compact : IsCompact region
  window_region : baseEquiv '' closure (window : Set JetPolynomial.Base) ⊆ region
  openRegion : Set SmallModes.Base
  open_region : IsOpen openRegion
  region_open : region ⊆ openRegion
  normal : SmallModes.Base → NormalFrame.Vec
  normal_smooth : ContDiffOn ℝ ∞ normal openRegion
  immersion : ∀ x ∈ openRegion, Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F) x)
  normal_properties : ∀ x ∈ openRegion,
    coordDeriv dx (A.phaseRealChartMap i e.symm F) x ⬝ᵥ normal x = 0 ∧
    coordDeriv dy (A.phaseRealChartMap i e.symm F) x ⬝ᵥ normal x = 0 ∧ normal x ⬝ᵥ normal x = 1
  convexity : ∀ x ∈ openRegion, 0 < coordinateMetricHessian
    (inducedCoordinateMetric (A.phaseRealChartMap i e.symm F)) Prod.fst x dy dy
  boundary : ∀ x ∈ region, amplitude x = 0 →
    realSecondForm (A.phaseRealChartMap i e.symm F) dy dy x ≠ 0 ∧
    normalize (realSecondForm (A.phaseRealChartMap i e.symm F) dy dy x) ≠ -normal x
  tensor : A.bundleRestore A.tensorTriv i
    (fun y => fiberFromThree (localizedTensorPullback e cutoff (fun q => ![(amplitude (baseEquiv q))^2,0,0]) y)) =
      fun p => (amp p)^2 • SmoothingAtlas.phaseDifferentialSquare phi p

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem supported_primitive_patch (i : A.centers) {F : M → Space}
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (houter : ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1))
    (hcover : (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {D : Set M} (hDs : closure D ⊆ (surfacePhaseChart (i : M) e).source)
    (hactive : ∀ p ∈ closure D, A.weight i p ≠ 0)
    {amp phi : M → ℝ} (hamp : ContMDiff planeModel 𝓘(ℝ) ∞ amp)
    (hamp0 : ∀ p, 0 ≤ amp p) (hamppos : ∀ p, 0 < amp p ↔ p ∈ D)
    (hphi : ∀ p ∈ D, phi =ᶠ[𝓝 p] (fun q => (e (chart (i : M) q)) 0))
    {V U : Set SmallModes.Base} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hDV : (surfacePhaseChart (i : M) e) '' closure D ⊆ V)
    (heV : MapsTo e e.source (baseEquiv ⁻¹' V))
    (hU : IsOpen U) (hVU : closure V ⊆ U)
    {n : SmallModes.Base → NormalFrame.Vec} (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ x ∈ U, Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F) x))
    (hN : ∀ x ∈ U, coordDeriv dx (A.phaseRealChartMap i e.symm F) x ⬝ᵥ n x = 0 ∧
      coordDeriv dy (A.phaseRealChartMap i e.symm F) x ⬝ᵥ n x = 0 ∧ n x ⬝ᵥ n x = 1)
    (hH : ∀ x ∈ U, 0 < coordinateMetricHessian
      (inducedCoordinateMetric (A.phaseRealChartMap i e.symm F)) Prod.fst x dy dy)
    (hb : ∀ x ∈ closure V \ (surfacePhaseChart (i : M) e) '' D,
      realSecondForm (A.phaseRealChartMap i e.symm F) dy dy x ≠ 0 ∧
      normalize (realSecondForm (A.phaseRealChartMap i e.symm F) dy dy x) ≠ -n x) :
    Nonempty (SupportedPrimitivePatch A i e F amp phi D) := by
  obtain ⟨K,hK,hKt,hs,hKA,hDK,hKa,χ,hχ,hχc,hχs,hχone,a,ha,ha0,haf,hapos,haoff,htensor⟩ :=
    A.constructed_primitive_support i e he hi hDs hactive hamp hamp0 hamppos hphi
  have hKS : K ⊆ (phaseWindow hV : Set JetPolynomial.Base) := by
    apply A.phaseSupport_window i e hKt hKA hV
    rwa [hs]
  refine ⟨{
    phase_smooth := he, inverse_smooth := hi,
    outer := houter, cover := hcover, cutoff := χ, cutoff_smooth := hχ,
    cutoff_compact := hχc, cutoff_source := hχs, amplitude := a, amplitude_smooth := ha,
    amplitude_nonneg := ha0, amplitude_surface := haf, amplitude_positive := hapos,
    compactSet := K, compact := hK, target := hKt, support := hs, inverse_support := hKA,
    cutoff_one := hχone, amplitude_off := haoff, compact_active := hKa,
    closed_coordinates := hDK, source_closed := hDs, active_closed := hactive,
    window := phaseWindow hV, window_compact := phaseWindow_compact hV hVc,
    phase_window := heV, support_window := hKS, region := closure V, region_compact := hVc,
    window_region := ?_, openRegion := U, open_region := hU, region_open := hVU,
    normal := n, normal_smooth := hn, immersion := hI, normal_properties := hN,
    convexity := hH, boundary := ?_, tensor := htensor }⟩
  · rw [phaseWindow_real_closure]
  · intro x hx ha0x
    apply hb x ⟨hx,?_⟩
    intro hin
    have hp := (hapos x).mpr hin
    rw [ha0x] at hp
    exact lt_irrefl _ hp

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
