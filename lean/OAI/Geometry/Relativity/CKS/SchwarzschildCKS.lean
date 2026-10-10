import OAI.Geometry.Relativity.CKS.SchwarzschildMetric
import OAI.Geometry.Relativity.CKS.SchwarzschildEnd
import OAI.Geometry.Relativity.CKS.SchwarzschildCKSDecay

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMixedGeometry CKSAngularSlice
open CKSSourceExterior
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

theorem four_atLeastTwo : Nat.AtLeastTwo 4 := inferInstance

attribute [local instance] four_atLeastTwo
attribute [local instance] CKSMixedGeometry.pointDimension_neZero CKSBoundarySurface.two_atLeastTwo

lemma tensorPatch_zero_smooth (n : Sphere) :
    ∀ i k : CKSMixedGeometry.I, i≠0 → k≠0 →
      ContDiffOn ℝ ∞ (fun _ : Angle => (0 : ℝ))
        (Metric.ball ((stereoSmoothPatch (-n)).chart n) 1) :=
  fun _ _ _ _ => contDiffOn_const

lemma tensorPatch_metric_CKS {m : ℝ} (hm : 0 < m) (n : Sphere) :
    SourceCKSComponents 3 6 (angularRadialTail (4*m+4) (Metric.ball ((stereoSmoothPatch (-n)).chart n) 1))
      (fun i k y => if i=0 ∧ k=0 then radialCoefficient m (y 0) else 0) (fun _ => 2*m) (fun _ _ _ => 0) := by
  constructor
  · simpa [ordinaryLeadingComponent,div_eq_mul_inv,mul_comm] using
      (radial_decay hm ((stereoSmoothPatch (-n)).chart n)).1
  · intro i k h
    have hn : ¬(i=0 ∧ k=0) := by tauto
    simpa only [ite_eq_right hn] using source_zero 3 3 (4*m+4)
      ((stereoSmoothPatch (-n)).chart n) (by positivity)
  · intro i k hi hk
    have hn : ¬(i=0 ∧ k=0) := by tauto
    simpa [ite_eq_right hn,ordinaryLeadingComponent] using source_zero 3 2 (4*m+4)
      ((stereoSmoothPatch (-n)).chart n) (by positivity)

lemma tensorPatch_second_CKS {m : ℝ} (hm : 0 < m) (n : Sphere) :
    SourceCKSComponents 2 5 (angularRadialTail (4*m+4) (Metric.ball ((stereoSmoothPatch (-n)).chart n) 1))
      (fun i k y => if i=0 ∧ k=0 then radialCoefficient m (y 0) else 0) (fun _ => 0) (fun _ _ _ => 0) := by
  constructor
  · simpa [ordinaryLeadingComponent] using
      (radial_decay hm ((stereoSmoothPatch (-n)).chart n)).2
  · intro i k h
    have hn : ¬(i=0 ∧ k=0) := by tauto
    simpa only [ite_eq_right hn] using source_zero 2 3 (4*m+4)
      ((stereoSmoothPatch (-n)).chart n) (by positivity)
  · intro i k hi hk
    have hn : ¬(i=0 ∧ k=0) := by tauto
    simpa [ite_eq_right hn,ordinaryLeadingComponent] using source_zero 2 2 (4*m+4)
      ((stereoSmoothPatch (-n)).chart n) (by positivity)

def tensorPatch {m : ℝ} (hm : 0 < m) (n : Sphere) : CKSTensorPatch where
  patch := stereoSmoothPatch (-n)
  region := Metric.ball ((stereoSmoothPatch (-n)).chart n) 1
  open_region := Metric.isOpen_ball
  region_target := by simp [stereoSmoothPatch]
  radius := 4*m+4
  metric := fun i k y => if i=0 ∧ k=0 then radialCoefficient m (y 0) else 0
  second := fun i k y => if i=0 ∧ k=0 then radialCoefficient m (y 0) else 0
  mr := fun _ => 2*m
  mg := fun _ _ _ => 0
  mK := fun _ _ _ => 0
  mr_smooth := contDiffOn_const
  mg_smooth := tensorPatch_zero_smooth n
  mK_smooth := tensorPatch_zero_smooth n
  metric_CKS := tensorPatch_metric_CKS hm n
  second_CKS := tensorPatch_second_CKS hm n
lemma tensorPatch_covers {m : ℝ} (hm : 0 < m) (n : Sphere) :
    n ∈ (tensorPatch hm n).patch.sphereRegion (tensorPatch hm n).region := by
  constructor
  · change n ∈ (stereoAngularChart (-n)).source
    simpa only [stereoAngularChart_source,mem_compl_iff,mem_singleton_iff] using
      ne_neg_of_mem_unit_sphere ℝ n
  · exact Metric.mem_ball_self (by norm_num)
lemma tensorPatch_realizes {m : ℝ} (hm : 0 < m) (n : Sphere) :
    (tensorPatch hm n).Realizes (metricPerturbation m) (tensorPerturbation m) := by
  intro y hy i k
  have hr : 4*m+4 < y 0 := hy.1
  have h := perturbation_polar m (stereoSmoothPatch (-n))
    (by linarith : 2*m+2 < y 0) (by linarith : 0 < y 0)
    (by simp [stereoSmoothPatch]) i k
  exact ⟨h.1.symm,h.2.symm⟩
lemma tensorPatch_aspect {m : ℝ} (hm : 0 < m) (n : Sphere) :
    (tensorPatch hm n).RepresentsMassAspect (fun _ => 4*m) := by
  intro p hp
  change cksChartMassAspect _ (fun _ => 2*m) (fun _ _ _ => 0) (fun _ _ _ => 0) _ = _
  rw [cksChartMassAspect_split]
  have hz (σ : AngularMatrix) : angularMetricTrace σ (fun _ _ => 0) = 0 := by
    change (σ⁻¹ * (0 : AngularMatrix)).trace = 0
    simp
  rw [hz]
  ring

lemma cksData_metric_smooth {m : ℝ} (hm : 0 < m) :
    ∀ y, (coordinateEnd hm).radius < ‖y‖ → ContDiffAt ℝ ∞ (metricPerturbation m) y :=
  fun y hy => (cartMetric_smoothAt hm (by change 2*m+1 < ‖y‖ at hy; linarith)).sub
    hyperbolicField_smooth.contDiffAt

lemma cksData_tensor_smooth {m : ℝ} (hm : 0 < m) :
    ∀ y, (coordinateEnd hm).radius < ‖y‖ → ContDiffAt ℝ ∞ (tensorPerturbation m) y :=
  fun y hy => (cartTensor_smoothAt hm (by change 2*m+1 < ‖y‖ at hy; linarith)).sub
    hyperbolicField_smooth.contDiffAt

lemma cksData_represents {m : ℝ} (hm : 0 < m) :
    ∀ p ∈ (coordinateEnd hm).domain,
      (smoothMetric hm).inner p = CKSSpatialManifold.endInner I3 (position m)
        (sourceSpatial (metricPerturbation m)) p ∧
      tensorInner m p = CKSSpatialManifold.endInner I3 (position m)
        (sourceSpatial (tensorPerturbation m)) p := by
  have hM : sourceSpatial (metricPerturbation m) = cartMetric m := by
    funext x
    change hyperbolicField x + (cartMetric m x - hyperbolicField x) = cartMetric m x
    abel
  have hK : sourceSpatial (tensorPerturbation m) = cartTensor m := by
    funext x
    change hyperbolicField x + (cartTensor m x - hyperbolicField x) = cartTensor m x
    abel
  intro p hp
  constructor
  · change metricInner m p = CKSSpatialManifold.endInner I3 (position m)
      (sourceSpatial (metricPerturbation m)) p
    rw [hM]
    rfl
  · rw [hK]
    rfl

lemma cksData_aspect_smooth (m : ℝ) :
    CKSSphericalHarmonics.SmoothSphere (fun _ => 4*m) := contMDiff_const

def cksData {m : ℝ} (hm : 0 < m) : CKSData (smoothMetric hm) (tensorInner m) where
  chart := coordinateEnd hm
  metricPerturbation := metricPerturbation m
  tensorPerturbation := tensorPerturbation m
  metric_smooth := cksData_metric_smooth hm
  tensor_smooth := cksData_tensor_smooth hm
  represents := cksData_represents hm
  massAspect := fun _ => 4*m
  aspect_smooth := cksData_aspect_smooth m
  patches := tensorPatch hm
  covers := tensorPatch_covers hm
  realizes := tensorPatch_realizes hm
  aspect_eq := tensorPatch_aspect hm
end CKSSchwarzschild

end

end OAI
