import OAI.Geometry.ProjectionBodies.Normalization

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma unitSegment_smul (y : Space n) (a : ℝ) : unitSegment (a • y)=a • unitSegment y := by
  rw [unitSegment,unitSegment,← image_smul,image_image]
  congr 1
  funext t
  exact smul_comm t a y

lemma unitSegment_image (T : Space n →ₗ[ℝ] Space n) (y : Space n) :
    T '' unitSegment y=unitSegment (T y) := by
  rw [unitSegment,unitSegment,image_image]
  congr 1
  funext a
  exact map_smul T a y

lemma unitSegment_zero : unitSegment (0:Space n)={0} := by
  ext x
  simp only [unitSegment,mem_image,mem_Icc,smul_zero,mem_singleton_iff]
  constructor
  · rintro ⟨a,ha,hax⟩;exact hax.symm
  · rintro rfl;exact ⟨0,by norm_num, rfl⟩

lemma segment_volume_support [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) (y : Space n) :
    volume.real (K+unitSegment y)=volume.real K+2*support (projectionBody K) y := by
  have hP := projectionBody_body hK hc h0
  have hne := hP.2.2.mono interior_subset
  by_cases hy : y=0
  · rw [hy,unitSegment_zero,add_singleton]
    simp only [add_zero,image_id']
    have hs0 : support (projectionBody K) 0=0 := by
      simpa using support_smul hP.1 hne (r :=0) le_rfl (0:Space n)
    simp only [hs0,mul_zero,add_zero]
  · let u : Spherical.Sphere n := ⟨‖y‖⁻¹ • y,by simp [norm_smul,hy]⟩
    have he : y=‖y‖ • (u:Space n) := by simp [u,smul_smul,hy]
    conv_lhs => rw [he,unitSegment_smul]
    rw [segment_volume u hK hc (norm_nonneg y)]
    conv_rhs => rhs;rhs;rw [he,support_smul hP.1 hne (norm_nonneg y),projectionBody_support_unit hK hc h0 u]
    ring

lemma linearEquiv_nhds (T : Space n ≃L[ℝ] Space n) {K : Set (Space n)}
    (h0 : K∈𝓝 (0:Space n)) : T '' K∈𝓝 (0:Space n) := by
  have hh := T.toHomeomorph.isOpenMap.image_mem_nhds h0
  change T '' K∈𝓝 (T 0) at hh
  simpa only [map_zero] using hh

lemma projection_support_linearEquiv [NeZero n] (T : Space n ≃L[ℝ] Space n)
    {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n))
    (y : Space n) : support (projectionBody (T '' K)) y=
      |LinearMap.det T.toLinearMap| * support (projectionBody K) (T.symm y) := by
  have him : T '' (K+unitSegment (T.symm y))=T '' K+unitSegment y := by
    change T.toLinearMap '' (K+unitSegment (T.symm y))=T.toLinearMap '' K+unitSegment y
    rw [image_add T.toLinearMap,unitSegment_image T.toLinearMap]
    change T.toLinearMap '' K+unitSegment (T (T.symm y))=_
    rw [T.apply_symm_apply]
  have hh := volumeReal_linearEquiv T (K+unitSegment (T.symm y))
  rw [him,segment_volume_support (hK.image T.continuous) (hc.linear_image T.toLinearMap)
    (linearEquiv_nhds T h0),segment_volume_support hK hc h0,volumeReal_linearEquiv] at hh
  linarith

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma adjoint_inverse_comp (T : Space n ≃L[ℝ] Space n) :
    T.toContinuousLinearMap.adjoint.toLinearMap.comp T.symm.toContinuousLinearMap.adjoint.toLinearMap=LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  change ⟪T.toContinuousLinearMap.adjoint (T.symm.toContinuousLinearMap.adjoint x),y⟫=⟪x,y⟫
  rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left]
  simp

/-- Invertibility of the transpose uses the transpose of the inverse. -/
def adjointEquiv (T : Space n ≃L[ℝ] Space n) : Space n ≃L[ℝ] Space n :=
  (LinearEquiv.ofLinearMap T.toContinuousLinearMap.adjoint.toLinearMap
    T.symm.toContinuousLinearMap.adjoint.toLinearMap
    (adjoint_inverse_comp T) (adjoint_inverse_comp T.symm)).toContinuousLinearEquiv

lemma adjointEquiv_clm (T : Space n ≃L[ℝ] Space n) :
    (adjointEquiv T).toContinuousLinearMap=T.toContinuousLinearMap.adjoint := rfl

lemma det_adjoint (A : Space n →L[ℝ] Space n) :
    LinearMap.det A.adjoint.toLinearMap=LinearMap.det A.toLinearMap := by
  let b := stdOrthonormalBasis ℝ (Space n)
  rw [← LinearMap.det_toMatrix b.toBasis,← ContinuousLinearMap.adjoint_toLinearMap,
    LinearMap.toMatrix_adjoint,Matrix.det_conjTranspose,LinearMap.det_toMatrix]
  exact star_trivial _

lemma adjointEquiv_det (T : Space n ≃L[ℝ] Space n) :
    LinearMap.det (adjointEquiv T).toLinearMap=LinearMap.det T.toLinearMap := det_adjoint _

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ} [NeZero n]

/-- The actual unpolarized projection body transforms by the determinant and
inverse transpose, proved from orthogonal shadow volumes via segment addition. -/
theorem projectionBody_linearEquiv (T : Space n ≃L[ℝ] Space n)
    {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) :
    projectionBody (T '' K)=|LinearMap.det T.toLinearMap| • (adjointEquiv T.symm '' projectionBody K) := by
  let P := projectionBody K
  let S := adjointEquiv T.symm
  let d := |LinearMap.det T.toLinearMap|
  have hd : 0<d := abs_pos.mpr (linearEquiv_det_ne_zero T)
  have hP : IsConvexBody P := projectionBody_body hK hc h0
  have hS := linearEquiv_body S hP
  have hR := smul_body hS hd.ne'
  have hL := projectionBody_body (hK.image T.continuous) (hc.linear_image T.toLinearMap) (linearEquiv_nhds T h0)
  apply (support_eq_iff hL.1 hL.2.1 (hL.2.2.mono interior_subset) hR.1 hR.2.1 (hR.2.2.mono interior_subset)).mp
  funext y
  rw [projection_support_linearEquiv T hK hc h0]
  change d*support P (T.symm y)=support (d • (S '' P)) y
  rw [support_smul_set hS.1 (hS.2.2.mono interior_subset) hd.le]
  change d*support P (T.symm y)=d*support (S.toContinuousLinearMap '' P) y
  rw [support_linear_image hP.1 (hP.2.2.mono interior_subset),adjointEquiv_clm,
    ContinuousLinearMap.adjoint_adjoint]
  rfl

lemma projection_volume_linearEquiv (T : Space n ≃L[ℝ] Space n)
    {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) :
    volume.real (projectionBody (T '' K))=|LinearMap.det T.toLinearMap|^(n-1)*volume.real (projectionBody K) := by
  rw [projectionBody_linearEquiv T hK hc h0,volumeReal_smul_nonneg (abs_nonneg _),
    finrank_euclideanSpace_fin,volumeReal_linearEquiv,adjointEquiv_det]
  rw [show T.symm.toLinearMap=(T.toLinearEquiv.symm : Space n →ₗ[ℝ] Space n) from rfl,
    LinearEquiv.det_coe_symm,abs_inv]
  have hd := abs_pos.mpr (linearEquiv_det_ne_zero T)
  have he : n=(n-1)+1 := by have := NeZero.pos n;omega
  have hp := congrArg (fun k : ℕ => |LinearMap.det T.toLinearMap|^k) he
  simp only [pow_succ] at hp
  rw [hp]
  field_simp

lemma projectionRatio_linearEquiv (T : Space n ≃L[ℝ] Space n)
    {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) :
    projectionRatio (T '' K)=projectionRatio K := by
  rw [projectionRatio,projection_volume_linearEquiv T hK hc h0,volumeReal_linearEquiv,
    projectionRatio,mul_pow]
  have hd := abs_pos.mpr (linearEquiv_det_ne_zero T)
  field_simp

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma projectionBody_unitBall : projectionBody (unitBall n)=kappa (n-1) • unitBall n := by
  have he : projectionBody (unitBall n)=wulff (fun _ : Spherical.Sphere n => kappa (n-1)) := by
    ext x
    constructor
    · intro hx u
      have hh := hx (u:Space n) (Spherical.norm_coe u)
      rwa [shadowVolume_unitBall u] at hh
    · intro hx u hu
      let v : Spherical.Sphere n := ⟨u,by simpa only [mem_sphere,dist_zero_right] using hu⟩
      have hh : ⟪u,x⟫≤kappa (n-1) := hx v
      have hv : shadowVolume (unitBall n) u=kappa (n-1) := shadowVolume_unitBall v
      rwa [hv]
  rw [he]
  have hb : wulff (fun _ : Spherical.Sphere n => kappa (n-1))=closedBall (0:Space n) (kappa (n-1)) :=
    Subset.antisymm (wulff_subset_closedBall (kappa_pos (n-1)).le (fun _ => le_rfl))
      (closedBall_subset_wulff (fun _ => le_rfl))
  rw [hb,unitBall,smul_closedBall' (kappa_pos (n-1)).ne']
  simp only [smul_zero,Real.norm_of_nonneg (kappa_pos (n-1)).le,mul_one]

lemma projectionRatio_unitBall {n : ℕ} (hn : 2≤n) : projectionRatio (unitBall n)=pettyConstant n := by
  let : NeZero n := ⟨by omega⟩
  rw [projectionRatio_normalized hn rfl,projectionBody_unitBall,
    normalizedVolume_smul (kappa_pos (n-1)).le,normalizedVolume_of_volume (K :=unitBall n) rfl,mul_one]
  rfl

/-- All affine ellipsoids, including arbitrary translates, attain equality. -/
theorem ellipsoid_projectionRatio {n : ℕ} (hn : 2≤n) {K : Set (Space n)}
    (hK : IsEllipsoid K) : projectionRatio K=pettyConstant n := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨a,T,rfl⟩ := hK
  have he : (fun x : Space n => a+T x) '' unitBall n=(fun y => a+y) '' (T '' unitBall n) := by
    rw [image_image]
  rw [he,projectionRatio_translate]
  change projectionRatio (T.toContinuousLinearEquiv '' unitBall n)=_
  rw [projectionRatio_linearEquiv T.toContinuousLinearEquiv unitBall_body.1 unitBall_body.2.1 unitBall_nhds,
    projectionRatio_unitBall hn]

end PettyProjection
end

end OAI
