import OAI.Geometry.SurfaceImmersion.Primitive.ReferenceCircularAtlas
import OAI.Geometry.SurfaceImmersion.Primitive.IndependentCircularRealization
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveOperator

namespace OAI

/-! The selected reference atlas supplies the actual identity operator,
smooth coefficient germs, and positive metric coefficients. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

def localPhases := d.B.centeredPhaseFamily (fun i => (d.P i).ξ) d.L

def basis := d.B.centeredAtlasBasis d.P (fun i => (d.P i).ξ) d.L

def globalPhases := d.B.curvedAtlasPhase d.localPhases

omit [CompactSpace M] in
lemma supported (i : d.B.centers) :
    tsupport (d.B.weight i) ⊆ circularDiskClosure (i : M) (d.radius i) :=
  circular_weight_support d.radius d.region d.weight_nonneg d.weight_positive i

omit [CompactSpace M] in
lemma basis_covectors (i : d.B.centers) {p : M} (hp : p ∈ tsupport (d.B.weight i)) :
    (d.basis i (chart (i : M) p)).ξ =
      fun j => phaseDerivative (d.localPhases i j) (coordinateChart (i : M) p) :=
  centeredSpatialBasis_covectors _ _ _ _ _ (d.admissible i p (d.supported i hp))

omit [CompactSpace M] in
lemma basis_smooth (i : d.B.centers) {p : M} (hp : p ∈ tsupport (d.B.weight i)) (j : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => (d.basis i y).Q j) (chart (i : M) p) := by
  exact (centeredSpatialBasis_coefficient_smoothAt _ _ _ _
    (d.admissible i p (d.supported i hp)) j).comp (chart (i : M) p)
      JetPolynomial.planeCoordinateIsometry.contDiff.contDiffAt

omit [CompactSpace M] in
lemma operator_identity (p : M) :
    d.B.primitiveFullOperator d.basis (fun a => d.B.weight a.1) d.globalPhases p =
      ContinuousLinearMap.id ℝ (CovariantTwoTensor p) :=
  d.B.primitiveFullOperator_reference d.basis d.localPhases
    (fun _ _ => centeredConvexPhase_smooth _ _ _) d.outer
    (fun i _ _p hp => congrFun (d.basis_covectors i hp) _) p

omit [CompactSpace M] in
lemma coefficient_positive (i : d.B.centers) {p : M} (hp : p ∈ tsupport (d.B.weight i)) (j : Fin 3) :
    0 < d.B.primitiveCoefficientField d.basis (i,j) p (gref.inner p) := by
  have hm := d.B.tensorPlaneRead_metric_on_weight gref i hp
  change d.B.tensorChartRead i gref.inner
    (JetPolynomial.planeCoordinateIsometry.symm (JetPolynomial.planeCoordinateIsometry (chart (i : M) p))) =
    coordinateMetric gref (i : M) (coordinateChart (i : M) p) at hm
  rw [LinearIsometryEquiv.symm_apply_apply] at hm
  rw [d.B.tensorChartRead_on_weight i gref.inner hp] at hm
  change 0 < (d.basis i (chart (i : M) p)).Q j
    (fiberToThree (d.B.bundleComponent d.B.tensorTriv i gref.inner p))
  rw [hm]
  exact d.positive i p (d.supported i hp) j

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
