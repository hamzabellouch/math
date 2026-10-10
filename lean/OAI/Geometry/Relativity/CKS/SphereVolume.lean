import OAI.Geometry.Relativity.CKS.SphereConeChart
import OAI.Geometry.Relativity.CKS.SphereConeMeasure

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal Pointwise
namespace CKSSchwarzschild
open CKSBoundarySurface CKSSurfaceVolume
local instance sphereVolumeFinrank : Fact (Module.finrank ℝ E3 = 2+1) := ⟨by simp⟩

lemma sphereCone_injOn (p : Sphere) {s : Set E2} (hs : s ⊆ (extChartAt I2 p).target) :
    InjOn (sphereCone p) (join '' (Ioo (0 : ℝ) 1 ×ˢ s)) := by
  rintro z ⟨⟨r,y⟩,⟨hr,hy⟩,rfl⟩ w ⟨⟨t,x⟩,⟨ht,hx⟩,rfl⟩ he
  simp only [sphereCone,join_zero,drop_join] at he
  have hn := congrArg norm he
  simp only [norm_smul,sphereParam_norm,mul_one,Real.norm_eq_abs,abs_of_pos hr.1,abs_of_pos ht.1] at hn
  subst t
  have hparam : sphereParam p y = sphereParam p x :=
    (smul_right_injective E3 (ne_of_gt hr.1)) he
  have hinv : (extChartAt I2 p).symm y = (extChartAt I2 p).symm x := Subtype.ext hparam
  have heq : y=x := (extChartAt I2 p).symm.injOn (hs hy) (hs hx) hinv
  rw [heq]

lemma sphereCone_image (p : Sphere) (s : Set Sphere) :
    sphereCone p '' (join '' (Ioo (0 : ℝ) 1 ×ˢ chartPreimage p s)) =
      Ioo (0 : ℝ) 1 • ((Subtype.val : Sphere → E3) '' (s ∩ (extChartAt I2 p).source)) := by
  ext z
  constructor
  · rintro ⟨w,⟨⟨r,y⟩,⟨hr,hy⟩,rfl⟩,rfl⟩
    refine ⟨r,hr,sphereParam p y,?_,?_⟩
    · exact ⟨(extChartAt I2 p).symm y,⟨hy.1,(extChartAt I2 p).map_target hy.2⟩,rfl⟩
    · simp [sphereCone]
  · rintro ⟨r,hr,n,⟨q,⟨hqs,hqp⟩,rfl⟩,rfl⟩
    refine ⟨join (r,extChartAt I2 p q),?_,?_⟩
    · refine ⟨(r,extChartAt I2 p q),⟨hr,?_,(extChartAt I2 p).map_source hqp⟩,rfl⟩
      change (extChartAt I2 p).symm (extChartAt I2 p q) ∈ s
      rwa [(extChartAt I2 p).left_inv hqp]
    · simp only [sphereCone,join_zero,drop_join,sphereParam,(extChartAt I2 p).left_inv hqp]

lemma sphere_toSphere_local (p : Sphere) {s : Set Sphere} (hs : MeasurableSet s) :
    (volume : Measure E3).toSphere (s ∩ (extChartAt I2 p).source) =
      localVolume sphereMetric.toContinuousRiemannianMetric p s := by
  let D := chartPreimage p s
  let U := join '' (Ioo (0:ℝ) 1 ×ˢ D)
  have hD : MeasurableSet D := chartPreimage_measurable p hs
  have hU : MeasurableSet U := splitEuclidean.symm.measurableEmbedding.measurableSet_image.mpr
    (measurableSet_Ioo.prod hD)
  have hd : ∀ z ∈ U, HasFDerivWithinAt (sphereCone p) (sphereConeDeriv p z) U z := by
    rintro z ⟨⟨r,y⟩,⟨hr,hy⟩,rfl⟩
    apply (sphereCone_hasFDerivAt p ?_).hasFDerivWithinAt
    simpa only [drop_join] using hy.2
  have hJ := lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure E3) hU hd
    (sphereCone_injOn p (fun y hy => hy.2))
  have hf : AEMeasurable (chartDensity sphereMetric.toContinuousRiemannianMetric p) (volume.restrict D) :=
    ((chartDensity_continuousOn sphereMetric.toContinuousRiemannianMetric p).mono
      (fun y hy => hy.2)).aemeasurable hD
  calc
    (volume : Measure E3).toSphere (s ∩ (extChartAt I2 p).source) =
        3 * volume (sphereCone p '' U) := by
      rw [Measure.toSphere_apply' _ (hs.inter (isOpen_extChartAt_source p).measurableSet)]
      simp only [E3,finrank_euclideanSpace, Fintype.card_fin,Nat.cast_ofNat]
      rw [sphereCone_image]
    _ = 3 * ∫⁻ z in U, ENNReal.ofReal |(sphereConeDeriv p z).det| := by rw [hJ]
    _ = 3 * (ENNReal.ofReal (1/3:ℝ) * ∫⁻ y in D,
        ENNReal.ofReal (chartDensity sphereMetric.toContinuousRiemannianMetric p y)) := by
      simp_rw [sphereCone_det]
      rw [lintegral_join_product D _ hf]
    _ = localVolume sphereMetric.toContinuousRiemannianMetric p s := by
      rw [localVolume_apply _ _ hs,← mul_assoc]
      have hnum : (3 : ℝ≥0∞) * ENNReal.ofReal (1/3 : ℝ) = 1 := by
        rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
      rw [hnum,one_mul]

theorem sphere_induced_volume :
    CKSSurfaceVolume.riemannianVolume sphereMetric.toContinuousRiemannianMetric =
      (volume : Measure CKSBoundarySurface.E3).toSphere := by
  apply volume_unique sphereMetric.toContinuousRiemannianMetric
    (riemannianVolume_isVolume _)
  intro p
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs]
  exact sphere_toSphere_local p hs

end CKSSchwarzschild

end

end OAI
