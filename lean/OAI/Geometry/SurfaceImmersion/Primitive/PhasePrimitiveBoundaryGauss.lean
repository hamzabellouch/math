import OAI.Geometry.SurfaceImmersion.Primitive.PhasePrimitiveMetricRead
import OAI.Geometry.SurfaceImmersion.Geometry.AmplitudeBoundaryMetric
import OAI.Geometry.SurfaceImmersion.Geometry.OrderedBoundaryInvariant
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricRegularity
import OAI.Geometry.SurfaceImmersion.Geometry.InverseTensorPullback
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricRead
import OAI.Geometry.SurfaceImmersion.Geometry.LocalizedTensorPullbackBound
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasTensorTransition

namespace OAI

/-! A tensor restored in a chart reads back exactly where its outer cutoff is one. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates
local instance boundaryGaussReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance boundaryGaussReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance boundaryGaussReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance boundaryGaussReadDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance boundaryGaussReadSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance boundaryGaussReadSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseMetricRead_primitive_germ (i : A.centers)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (g h : SmoothMetric M) (χ : Base → ℝ) (a : SmallModes.Base → ℝ)
    (htarget : h.inner = g.inner + A.bundleRestore A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {x : SmallModes.Base} (hx : baseEquiv.symm x ∈ e.target)
    (hactive : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0) :
    A.phaseMetricRead i e.symm h =ᶠ[𝓝 x] fun y => A.phaseMetricRead i e.symm g y +
      χ (e.symm (baseEquiv.symm y)) • ![(a y)^2,0,0] := by
  have ht := (e.open_target.preimage baseEquiv.symm.continuous).mem_nhds hx
  have hn := (isOpen_ne.preimage ((A.chartWeight_smooth i).continuous.comp
    (hi.continuous.comp baseEquiv.symm.continuous))).mem_nhds hactive
  filter_upwards [ht,hn] with y hy hya
  have hh := A.phaseMetricRead_primitive i e he hi g h χ a htarget hy hya
  simpa only [baseEquiv.apply_symm_apply] using hh

lemma phase_primitive_gauss_zero (i : A.centers)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (g h : SmoothMetric M) {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (htarget : h.inner = g.inner + A.bundleRestore A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {x : SmallModes.Base} (hx : baseEquiv.symm x ∈ e.target)
    (hactive : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0)
    (hz : a x = 0) (hnonneg : ∀ᶠ y in 𝓝 x, 0 ≤ a y) :
    RealModes.coordinateGauss (fun y => A.phaseMetricRead i e.symm h y 0)
      (fun y => A.phaseMetricRead i e.symm h y 1) (fun y => A.phaseMetricRead i e.symm h y 2) x =
    RealModes.coordinateGauss (fun y => A.phaseMetricRead i e.symm g y 0)
      (fun y => A.phaseMetricRead i e.symm g y 1) (fun y => A.phaseMetricRead i e.symm g y 2) x := by
  have heq := A.phaseMetricRead_primitive_germ i e he hi g h χ a htarget hx hactive
  have h0 := heq.mono (fun y hy => congrFun hy 0)
  have h1 : (fun y => A.phaseMetricRead i e.symm h y 1) =ᶠ[𝓝 x]
      (fun y => A.phaseMetricRead i e.symm g y 1) :=
    heq.mono (fun y hy => by simpa using congrFun hy 1)
  have h2 : (fun y => A.phaseMetricRead i e.symm h y 2) =ᶠ[𝓝 x]
      (fun y => A.phaseMetricRead i e.symm g y 2) :=
    heq.mono (fun y hy => by simpa using congrFun hy 2)
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero] at h0
  rw [RealModes.coordinateGauss_germ h0 h1 h2]
  exact RealModes.coordinateGauss_add_factor_square_boundary
    (contDiff_pi.mp (A.phaseMetricRead_smooth i hi g) 0) ha
    (hχ.comp (hi.comp baseEquiv.symm.contDiff)) hz hnonneg

/-- At a zero of the amplitude, the original immersion's ordered crossing
invariant is exactly the scalar boundary expression for the new metric. -/
lemma phase_primitive_boundary_crossing (i : A.centers)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (h : SmoothMetric M) {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (htarget : h.inner = g.inner + A.bundleRestore A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {x : SmallModes.Base} (hx : baseEquiv.symm x ∈ e.target)
    (hactive : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0)
    (hz : a x = 0) (hnonneg : ∀ᶠ y in 𝓝 x, 0 ≤ a y)
    (hD : NormalFrame.gramDet
      (SmallModes.coordDeriv SmallModes.dx (A.phaseRealChartMap i e.symm F) x)
      (SmallModes.coordDeriv SmallModes.dy (A.phaseRealChartMap i e.symm F) x) ≠ 0)
    (hB : RealModes.realSecondForm (A.phaseRealChartMap i e.symm F)
      SmallModes.dy SmallModes.dy x ≠ 0) (b c : ℝ) :
    let H := A.phaseRealChartMap i e.symm F
    let κ := RealModes.coordinateGaussianCurvature
      (RealModes.realMetric H SmallModes.dx SmallModes.dx)
      (RealModes.realMetric H SmallModes.dx SmallModes.dy)
      (RealModes.realMetric H SmallModes.dy SmallModes.dy) x
    VelocityFrame.orderedCrossing H SmallModes.dy (b,c) x κ =
      ((SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dx H) x ⬝ᵥ
        VelocityFrame.normalize (RealModes.realSecondForm H SmallModes.dy SmallModes.dy x))*b +
        Real.sqrt (RealModes.realSecondForm H SmallModes.dy SmallModes.dy x ⬝ᵥ
          RealModes.realSecondForm H SmallModes.dy SmallModes.dy x)*c)^2 +
        (RealModes.coordinateGauss (fun y => A.phaseMetricRead i e.symm h y 0)
          (fun y => A.phaseMetricRead i e.symm h y 1)
          (fun y => A.phaseMetricRead i e.symm h y 2) x)*b^2 := by
  dsimp only
  rw [VelocityFrame.orderedCrossing_dy (A.phaseRealChartMap_smooth i hi hF.1) x hD hB,
    ← RealModes.coordinateGauss_eq_curvature_mul _ _ hD,
    A.phaseGauss_isometry i hi hF hactive,
    ← A.phase_primitive_gauss_zero i e he hi g h hχ ha htarget hx hactive hz hnonneg]
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
