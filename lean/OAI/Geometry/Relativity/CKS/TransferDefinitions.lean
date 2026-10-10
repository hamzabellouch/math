import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.SourceExteriorDefinitions
import OAI.Geometry.Relativity.CKS.SourceTopology
import OAI.Geometry.Relativity.CKS.SourceReplacementDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildHorizonExclusionDefinitions

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
namespace CKSMain
universe u v
attribute [local instance] manifold_regular

variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

def WeakFutureBoundary (q : SmoothMetric I3 (M := N)) (k : InnerField I3 (M := N)) : Prop :=
  ∃ B : BoundaryGeometry q k, ∀ p, B.thetaPlus p ≤ 0

attribute [local instance] CKSBoundarySurface.halfSpaceDimension_neZero
  CKSBoundarySurface.two_atLeastTwo CKSLorentz.hsgNorm CKSLorentz.hsgSpace
  CKSMetricGluing.real_continuousAdd CKSMetricGluing.real_continuousConstSMul
  CKSMetricGluing.real_smulCommClass CKSSpatialManifold.real_id_isometric
  CKSSpatialManifold.covector_smulCommClass CKSLorentz.real_isTopologicalAddGroup
  CKSInducedArea.scalar_smulCommClass CKSInducedArea.scalar_vectorBundle
  CKSInducedArea.scalar_continuousSMul CKSSourceExterior.source_manifold_one
  CKSSchwarzschild.frameCovectorModule

theorem af_tangent_vectorBundle :
    VectorBundle ℝ E3 (fun x : N => TangentSpace I3 x) := inferInstance

attribute [local instance] af_tangent_vectorBundle

theorem af_covector_vectorBundle :
    VectorBundle ℝ (E3 →L[ℝ] ℝ) (fun x : N => TangentSpace I3 x →L[ℝ] ℝ) :=
  inferInstance

attribute [local instance] af_covector_vectorBundle

omit [IsManifold I3 ∞ N] in
theorem af_covector_topologicalAddGroup (point : N) :
    IsTopologicalAddGroup (TangentSpace I3 point →L[ℝ] ℝ) := inferInstance

omit [IsManifold I3 ∞ N] in
theorem af_covector_continuousSMul (point : N) :
    ContinuousSMul ℝ (TangentSpace I3 point →L[ℝ] ℝ) := inferInstance

attribute [local instance] af_covector_topologicalAddGroup af_covector_continuousSMul

attribute [local instance] sixteen_atLeastTwo

def WeakAFExteriorInequality : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace H3 X] [IsManifold I3 ∞ X]
    [T2Space X] [SecondCountableTopology X] [ConnectedSpace X]
    (q : SmoothMetric I3 (M := X)) (k : InnerField I3 (M := X)),
    letI := CKSMetricGluing.real_continuousAdd
    letI := CKSMetricGluing.real_continuousConstSMul
    letI := CKSMetricGluing.real_smulCommClass
    let tensorSection : X → TotalSpace SpatialBilinear
        (fun x : X => TangentSpace I3 x →L[ℝ] TangentSpace I3 x →L[ℝ] ℝ) :=
      innerSection I3 k
    ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ tensorSection →
    (∀ x v w, k x v w = k x w v) →
    Orientable (N := X) → IsCompact (I3.boundary X) → (I3.boundary X).Nonempty →
    CKSReplacementCompleteness.IsComplete I3 q.toContinuousRiemannianMetric →
    ∀ (c : CoordinateEnd (N := X)) (G L : SpatialTensor) (a E : ℝ) (P : Fin 3 → ℝ),
    (∀ x ∈ c.domain,
      let metricForm : SpatialBilinear := q.inner x
      let tensorForm : SpatialBilinear := k x
      metricForm = endInner I3 c.coordinate G x ∧
        tensorForm = endInner I3 c.coordinate L x) →
    1/2 < a →
    (∀ i j : Fin 3, CKSADM.SymbolN 2 a
      (fun x => spatialCartesian G x i j - if i=j then 1 else 0)) →
    (∀ i j : Fin 3, CKSADM.SymbolN 1 (1+a) (fun x => spatialCartesian L x i j)) →
    PhysicalDEC I3 q.inner k → constraintsIntegrable q k →
    Tendsto (spatialADMEnergy G) atTop (𝓝 E) →
    Tendsto (spatialADMMomentum G L) atTop (𝓝 P) →
    ‖(WithLp.toLp 2 P : EuclideanSpace ℝ (Fin 3))‖ < E →
    WeakFutureBoundary q k →
    Real.sqrt (CKSSourceExterior.minimumEnclosingArea q / (16*Real.pi)) ≤
      Real.sqrt (E^2 - ‖(WithLp.toLp 2 P : EuclideanSpace ℝ (Fin 3))‖^2)

end CKSMain

end

end OAI
