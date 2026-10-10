import OAI.Geometry.SurfaceImmersion.Atlas.TensorPhaseDifferential
import OAI.Geometry.SurfaceImmersion.Primitive.SpatialLoopAmplitude
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasSupportedWeights

namespace OAI

/-! The supported primitive tensor is positive semidefinite, so the target
of a primitive addition is an actual smooth Riemannian metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates

lemma amplitude_eq_zero_of_velocity_eq_normal {O : TopologicalSpace.Opens LowJet}
    (l : SurfaceVelocityFamily.Loop O) {J : LowJet} (hJ : J ∈ O)
    (hv : l.velocity (J,0) = SurfaceVelocityFamily.normal J) : l.amplitude J = 0 := by
  have hh := l.length J hJ 0
  rw [hv] at hh
  nlinarith [sq_nonneg (l.amplitude J)]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
local instance primitiveMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance primitiveMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance primitiveMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance primitiveMetricDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance primitiveMetricSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance primitiveMetricSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def primitiveTensor (i : A.centers) (a : JetPolynomial.Base → ℝ) : ∀ p : M, CovariantTwoTensor p :=
  A.bundleRestore A.tensorTriv i (fun y => fiberFromThree ![a y^2,0,0])

omit [CompactSpace M] in
lemma primitiveTensor_smooth (i : A.centers) {a : JetPolynomial.Base → ℝ}
    (ha : ContDiff ℝ ∞ a) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (A.primitiveTensor i a p)) := by
  apply A.bundleRestore_smooth A.tensorTriv A.tensorTriv_domain i
  apply fiberFromThree.contDiff.comp
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact ha.pow 2
  · exact contDiff_const
  · exact contDiff_const

omit [CompactSpace M] in
lemma primitiveTensor_symmetric (i : A.centers) (a : JetPolynomial.Base → ℝ)
    (p : M) (v w : TangentSpace planeModel p) :
    A.primitiveTensor i a p v w = A.primitiveTensor i a p w v := by
  by_cases hp : p ∈ (chart (i : M)).source
  · rw [primitiveTensor,A.tensorRestore_apply i _ hp,A.tensorRestore_apply i _ hp,
      fiberFromThree_symmetric]
  · have hz : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hp (A.outer_support i h))
    simp [primitiveTensor,bundleRestore,hz]

omit [CompactSpace M] in
lemma primitiveTensor_nonneg (i : A.centers) (a : JetPolynomial.Base → ℝ)
    (hzero : ∀ p ∈ tsupport (A.outer i), p ∉ tsupport (A.weight i) →
      a (chart (i : M) p) = 0) (p : M) (v : TangentSpace planeModel p) :
    0 ≤ A.primitiveTensor i a p v v := by
  by_cases ho : p ∈ tsupport (A.outer i)
  · rw [primitiveTensor,A.tensorRestore_apply i _ (A.outer_support i ho),fiberFromThree_apply]
    by_cases hw : p ∈ tsupport (A.weight i)
    · rw [A.outer_one i p hw]
      have hsquare (r t : ℝ) : 0 ≤ r^2*t*t := by nlinarith [sq_nonneg (r*t)]
      simpa [PhaseMean.evaluate] using hsquare (a (chart (i : M) p))
        (planeCoordinates ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p v)).1
    · rw [hzero p ho hw]
      simp [PhaseMean.evaluate]
  · have hz : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport ho
    simp [primitiveTensor,bundleRestore,hz]

def primitiveMetric (g : SmoothMetric M) (i : A.centers) (a : JetPolynomial.Base → ℝ)
    (ha : ContDiff ℝ ∞ a)
    (hzero : ∀ p ∈ tsupport (A.outer i), p ∉ tsupport (A.weight i) →
      a (chart (i : M) p) = 0) : SmoothMetric M where
  inner p := g.inner p+A.primitiveTensor i a p
  symm p v w := by
    change g.inner p v w+A.primitiveTensor i a p v w = _
    rw [g.symm p v w,A.primitiveTensor_symmetric i a p v w]
    rfl
  pos p v hv := lt_of_lt_of_le (g.pos p v hv)
    (le_add_of_nonneg_right (A.primitiveTensor_nonneg i a hzero p v))
  isVonNBounded p := (g.isVonNBounded p).subset (by
    intro v hv
    exact lt_of_le_of_lt (le_add_of_nonneg_right (A.primitiveTensor_nonneg i a hzero p v)) hv)
  contMDiff := g.contMDiff.add_section (A.primitiveTensor_smooth i ha)

lemma primitive_amplitude_zero_off_weight (i : A.centers)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {a : JetPolynomial.Base → ℝ} (hamp : l.HasSpatialAmplitude a)
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (houter : (chart (i : M)) '' tsupport (A.outer i) ⊆ S)
    (G : JetPolynomial.Base → JetPolynomial.Space) (hGO : MapsTo (lowJet G) S O)
    (K : Set JetPolynomial.Base) (hKA : K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hv : ∀ J ∈ O, lowJetPosition J ∉ K → ∀ t, l.velocity (J,t) = SurfaceVelocityFamily.normal J) :
    ∀ p ∈ tsupport (A.outer i), p ∉ tsupport (A.weight i) → a (chart (i : M) p) = 0 := by
  intro p hp hwp
  let x := chart (i : M) p
  have hx : x ∈ S := houter ⟨p,hp,rfl⟩
  have hxK : x ∉ K := by
    intro hk
    obtain ⟨q,hq,he⟩ := hKA hk
    have hqp : q = p := (chart (i : M)).injOn (A.weight_support i hq) (A.outer_support i hp) he
    exact hwp (hqp ▸ hq)
  rw [← l.amplitude_at_lowJet hamp G (hGO hx)]
  exact l.amplitude_eq_zero_of_velocity_eq_normal (hGO hx)
    (hv _ (hGO hx) (by simpa only [lowJetPosition_lowJet] using hxK) 0)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
