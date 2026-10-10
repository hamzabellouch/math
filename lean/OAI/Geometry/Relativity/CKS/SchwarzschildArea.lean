import OAI.Geometry.Relativity.CKS.CutAreaDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildBoundary
import OAI.Geometry.Relativity.CKS.SchwarzschildProjection
import OAI.Geometry.Relativity.CKS.SurfaceImage
import OAI.Geometry.Relativity.CKS.SphereVolume
import OAI.Geometry.Relativity.CKS.SchwarzschildAreaDefinitions

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace CKSSchwarzschild
open CKSBoundarySurface CKSFullCutArea CKSSurfaceVolume

lemma sphere_area : riemannianVolume sphereMetric.toContinuousRiemannianMetric univ =
    ENNReal.ofReal (4 * Real.pi) := by
  rw [sphere_induced_volume,Measure.toSphere_apply_univ,EuclideanSpace.volume_ball_fin_three]
  simp only [E3,finrank_euclideanSpace,Fintype.card_fin,Nat.cast_ofNat,ENNReal.ofReal_one,one_pow,one_mul]
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

lemma scaled_sphere_area {m : ℝ} (hm : 0 < m) :
    riemannianVolume (boundaryScaledMetric hm).toContinuousRiemannianMetric univ =
      ENNReal.ofReal (16 * Real.pi * m^2) := by
  rw [boundaryScaledMetric,riemannianVolume_scaled,Measure.smul_apply,smul_eq_mul,sphere_area,
    ← ENNReal.ofReal_mul (sq_nonneg (2*m))]
  congr 1
  ring

lemma full_cut_area_lower {m : ℝ} (hm : 0 < m) (D : CKSGeometricCuts.OuterDomain Exterior) :
    ENNReal.ofReal (16*Real.pi*m^2) ≤ area (smoothMetric hm) D := by
  let : MeasurableSpace (Surface D) := borel (Surface D)
  let : BorelSpace (Surface D) := ⟨rfl⟩
  rw [← scaled_sphere_area hm]
  apply volume_le_of_surjective_nonexpanding
    (cutMetric (smoothMetric hm) D).toContinuousRiemannianMetric
    (boundaryScaledMetric hm).toContinuousRiemannianMetric (angular ∘ cutInclusion D)
    ((angular_smooth.comp (cutInclusion_smooth D)).of_le (by simp))
    (full_cut_radial_projection_surjective D)
  intro x v
  rw [mfderiv_comp x (angular_smooth.mdifferentiable (by simp) _)
    ((cutInclusion_smooth D).mdifferentiable (by simp) _)]
  exact angular_metric_bound hm (cutInclusion D x) (mfderiv I2 I3 (cutInclusion D) x v)

lemma boundary_metric_formula {m : ℝ} (hm : 0 < m) (p : Boundary Exterior) (v : E2) :
    metricInner m p.val (liftPlane v) (liftPlane v) =
      (2*m)^2 * sphereMetric.inner (boundarySphere p) v v := by
  rw [metricInner_quad hm]
  have hh : radius m p.val = 2*m := by simp [radius,boundary_height p]
  rw [hh,liftPlane_zero,zero_pow (by decide : 2 ≠ 0),zero_div,zero_add]
  rw [sphereMetric_apply,real_inner_self_eq_norm_sq]
  congr 2
  have hd : ambientDerivative directionAmbient p.val (liftPlane v) =
      sphereDerivative (boundarySphere p) v := by
    change mfderiv I3 𝓘(ℝ,E3) directionAmbient p.val (liftPlane v) = _
    rw [mfderiv_directionAmbient]
    rfl
  exact congrArg norm hd

lemma boundary_area_upper {m : ℝ} (hm : 0 < m) :
    area (smoothMetric hm) (CKSGeometricCuts.identityOuterDomain boundary_compact) ≤
      ENNReal.ofReal (16*Real.pi*m^2) := by
  let D := CKSGeometricCuts.identityOuterDomain boundary_compact
  let : MeasurableSpace (Surface D) := borel (Surface D)
  let : BorelSpace (Surface D) := ⟨rfl⟩
  rw [← scaled_sphere_area hm]
  apply volume_le_of_surjective_nonexpanding
    (boundaryScaledMetric hm).toContinuousRiemannianMetric
    (cutMetric (smoothMetric hm) D).toContinuousRiemannianMetric boundarySphere.symm
    (boundarySphere_symm_smooth.of_le (by simp)) boundarySphere.symm.surjective
  intro x v
  change E2 at v
  change metricInner m (boundarySphere.symm x).val
    (mfderiv I2 I3 (Subtype.val : Boundary Exterior → Exterior) (boundarySphere.symm x)
      (mfderiv I2 I2 boundarySphere.symm x v))
    (mfderiv I2 I3 (Subtype.val : Boundary Exterior → Exterior) (boundarySphere.symm x)
      (mfderiv I2 I2 boundarySphere.symm x v)) ≤ _
  rw [mfderiv_boundarySphere_symm]
  change metricInner m (boundarySphere.symm x).val
    (mfderiv I2 I3 (Subtype.val : Boundary Exterior → Exterior) (boundarySphere.symm x) v)
    (mfderiv I2 I3 (Subtype.val : Boundary Exterior → Exterior) (boundarySphere.symm x) v) ≤ _
  rw [(CKSBoundarySurface.inclusion_hasMFDeriv _).mfderiv]
  change metricInner m (boundarySphere.symm x).val (liftPlane v) (liftPlane v) ≤
    (2*m)^2 * sphereMetric.inner x v v
  rw [boundary_metric_formula hm, boundarySphere.apply_symm_apply]

theorem full_minimum_enclosing_area {m : ℝ} (hm : 0 < m) :
    CKSFullCutArea.minEnclosingArea (smoothMetric hm) = ENNReal.ofReal (16 * Real.pi * m^2) := by
  apply le_antisymm
  · exact (iInf_le _ (CKSGeometricCuts.identityOuterDomain boundary_compact)).trans (boundary_area_upper hm)
  · exact le_iInf (full_cut_area_lower hm)

end CKSSchwarzschild

end

end OAI
