import OAI.Geometry.ProjectionBodies.WulffVariation

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection

lemma compact_convex_real_interval {C : Set ℝ} (hC : IsCompact C) (hc : Convex ℝ C)
    (hn : C.Nonempty) : C = Icc (sInf C) (sSup C) := by
  apply Subset.antisymm
  · exact fun x hx => ⟨csInf_le hC.bddBelow hx,le_csSup hC.bddAbove hx⟩
  · exact (convex_iff_ordConnected.mp hc).out (hC.sInf_mem hn) (hC.sSup_mem hn)

lemma compact_convex_real_add_interval_volume {C : Set ℝ} (hC : IsCompact C)
    (hc : Convex ℝ C) (hn : C.Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    volume (C+Icc (-t) t) = volume C+ENNReal.ofReal (2*t) := by
  rw [compact_convex_real_interval hC hc hn]
  have hab : sInf C ≤ sSup C := (hC.isGLB_sInf hn).1 (hC.sSup_mem hn)
  rw [Icc_add_Icc hab (by linarith),Real.volume_Icc,Real.volume_Icc,
    ← ENNReal.ofReal_add (sub_nonneg.mpr hab) (by positivity)]
  congr 1
  ring

section Product
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E] in
lemma compact_fiber {K : Set (E × ℝ)} (hK : IsCompact K) (x : E) :
    IsCompact (Prod.mk x ⁻¹' K) :=
  (IsClosedEmbedding.of_isEmbedding_isClosedMap (isEmbedding_prodMkRight x) (isClosedMap_prodMk_left x)).isCompact_preimage hK

omit [MeasureSpace E] [BorelSpace E] in
lemma convex_fiber {K : Set (E × ℝ)} (hc : Convex ℝ K) (x : E) :
    Convex ℝ (Prod.mk x ⁻¹' K) := by
  intro a ha b hb s t hs ht hst
  have h := hc ha hb hs ht hst
  change (x,s • a+t • b) ∈ K
  simpa only [Prod.smul_mk,Prod.mk_add_mk,← add_smul,hst,one_smul] using h

omit [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E] in
lemma fiber_vertical_add (K : Set (E × ℝ)) (I : Set ℝ) (x : E) :
    Prod.mk x ⁻¹' (K+(Prod.mk (0:E) '' I)) = (Prod.mk x ⁻¹' K)+I := by
  ext r
  constructor
  · rintro ⟨z,hz,_,⟨a,ha,rfl⟩,he⟩
    have hx : z.1 = x := by simpa only [Prod.fst_add,add_zero] using congrArg Prod.fst he
    refine ⟨z.2,?_,a,ha,?_⟩
    · change (x,z.2) ∈ K
      simpa only [← hx,Prod.mk.eta] using hz
    · exact congrArg Prod.snd he
  · rintro ⟨a,ha,b,hb,rfl⟩
    exact ⟨(x,a),ha,(0,b),⟨b,hb,rfl⟩,by simp only [Prod.mk_add_mk,add_zero]⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E] in
lemma fiber_nonempty_iff (K : Set (E × ℝ)) (x : E) :
    (Prod.mk x ⁻¹' K).Nonempty ↔ x ∈ Prod.fst '' K := by
  constructor
  · rintro ⟨r,hr⟩; exact ⟨(x,r),hr,rfl⟩
  · rintro ⟨⟨y,r⟩,hr,rfl⟩; exact ⟨r,hr⟩

/-- The actual Fubini segment-addition formula in orthogonal product coordinates. -/
theorem vertical_segment_volume {K : Set (E × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) {t : ℝ} (ht : 0 ≤ t) :
    volume (K+Prod.mk (0:E) '' Icc (-t) t) =
      volume K+ENNReal.ofReal (2*t)*volume (Prod.fst '' K) := by
  have hC : IsCompact (K+Prod.mk (0:E) '' Icc (-t) t) :=
    hK.add (isCompact_Icc.image (by fun_prop))
  have hP : MeasurableSet (Prod.fst '' K) := (hK.image continuous_fst).measurableSet
  rw [Measure.volume_eq_prod,Measure.prod_apply hC.measurableSet,
    Measure.prod_apply hK.measurableSet]
  have he : ∀ x : E, volume (Prod.mk x ⁻¹' (K+Prod.mk (0:E) '' Icc (-t) t)) =
      volume (Prod.mk x ⁻¹' K)+(Prod.fst '' K).indicator (fun _ => ENNReal.ofReal (2*t)) x := by
    intro x
    rw [fiber_vertical_add]
    by_cases hn : (Prod.mk x ⁻¹' K).Nonempty
    · rw [indicator_of_mem ((fiber_nonempty_iff K x).mp hn)]
      exact compact_convex_real_add_interval_volume (compact_fiber hK x) (convex_fiber hc x) hn ht
    · rw [not_nonempty_iff_eq_empty.mp hn,empty_add,measure_empty,
        indicator_of_notMem (fun h => hn ((fiber_nonempty_iff K x).mpr h)),add_zero]
  simp_rw [he]
  rw [lintegral_add_left (measurable_measure_prodMk_left hK.measurableSet),
    lintegral_indicator hP,lintegral_const,Measure.restrict_apply_univ]

end Product
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma perpendicular_inner {n : ℕ} (u : Space n) (z : perpendicular u) : ⟪u,(z : Space n)⟫ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.property

/-- Orthogonal coordinates with the last coordinate in a specified unit direction. -/
def shadowCoordLinear {n : ℕ} (u : Sphere n) :
    WithLp 2 (perpendicular (u : Space n) × ℝ) →ₗ[ℝ] Space n where
  toFun z := (WithLp.ofLp z).1+(WithLp.ofLp z).2 • (u : Space n)
  map_add' z w := by
    simp only [WithLp.ofLp_add,Prod.fst_add,Prod.snd_add,Submodule.coe_add,add_smul]
    abel
  map_smul' a z := by
    simp only [WithLp.ofLp_smul,Prod.smul_fst,Prod.smul_snd,Submodule.coe_smul_of_tower,
      smul_eq_mul,smul_add,smul_smul,RingHom.id_apply]

lemma shadowCoordLinear_inner {n : ℕ} (u : Sphere n)
    (z w : WithLp 2 (perpendicular (u : Space n) × ℝ)) :
    ⟪shadowCoordLinear u z,shadowCoordLinear u w⟫ = ⟪z,w⟫ := by
  change ⟪((WithLp.ofLp z).1 : Space n)+(WithLp.ofLp z).2 • (u : Space n),
    ((WithLp.ofLp w).1 : Space n)+(WithLp.ofLp w).2 • (u : Space n)⟫ = _
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq,norm_coe,one_pow,mul_one,
    perpendicular_inner,Submodule.mem_orthogonal_singleton_iff_inner_left.mp (WithLp.ofLp z).1.property]
  simp only [mul_zero,add_zero,zero_add,WithLp.prod_inner_apply,Submodule.coe_inner,Real.inner_apply]
  ring

lemma shadowCoordLinear_surjective {n : ℕ} (u : Sphere n) : Surjective (shadowCoordLinear u) := by
  intro x
  have hz : x-⟪(u : Space n),x⟫ • (u : Space n) ∈ perpendicular (u : Space n) := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,norm_coe,one_pow,mul_one,sub_self]
  refine ⟨WithLp.toLp 2 (⟨_,hz⟩,⟪(u : Space n),x⟫),?_⟩
  change x-_+_ = x
  exact sub_add_cancel _ _

def shadowCoords {n : ℕ} (u : Sphere n) :
    WithLp 2 (perpendicular (u : Space n) × ℝ) ≃ₗᵢ[ℝ] Space n :=
  LinearIsometryEquiv.ofSurjective
    (LinearMap.isometryOfInner (shadowCoordLinear u) (shadowCoordLinear_inner u))
    (shadowCoordLinear_surjective u)

lemma shadowCoords_apply {n : ℕ} (u : Sphere n) (z : perpendicular (u : Space n)) (t : ℝ) :
    shadowCoords u (WithLp.toLp 2 (z,t)) = z+t • (u : Space n) := rfl

lemma shadowCoords_projection {n : ℕ} (u : Sphere n)
    (z : perpendicular (u : Space n)) (t : ℝ) :
    (perpendicular (u : Space n)).orthogonalProjectionOnto
      (shadowCoords u (WithLp.toLp 2 (z,t))) = z := by
  rw [shadowCoords_apply,map_add,map_smul,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  have hz : (perpendicular (u : Space n)).orthogonalProjectionOnto (u : Space n) = 0 := by
    exact Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero (u : Space n)
  rw [hz,smul_zero,add_zero]

/-- The coordinate change preserves the actual standard Euclidean measures. -/
def shadowMeasurableEquiv {n : ℕ} (u : Sphere n) :
    (perpendicular (u : Space n) × ℝ) ≃ᵐ Space n :=
  (MeasurableEquiv.toLp 2 _).trans (shadowCoords u).toMeasurableEquiv

lemma shadowMeasurableEquiv_measurePreserving {n : ℕ} (u : Sphere n) :
    MeasurePreserving (shadowMeasurableEquiv u) :=
  (WithLp.volume_preserving_toLp _ _).trans (shadowCoords u).measurePreserving

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

def unitSegment {n : ℕ} (y : Space n) : Set (Space n) :=
  (fun a : ℝ => a • y) '' Icc (-1) 1

lemma unitSegment_compact {n : ℕ} (y : Space n) : IsCompact (unitSegment y) :=
  isCompact_Icc.image (by fun_prop)

lemma unitSegment_nonempty {n : ℕ} (y : Space n) : (unitSegment y).Nonempty :=
  ⟨0,⟨0,by norm_num,zero_smul ℝ y⟩⟩

lemma unitSegment_convex {n : ℕ} (y : Space n) : Convex ℝ (unitSegment y) :=
  (convex_Icc (-1:ℝ) 1).linear_image (LinearMap.toSpanSingleton ℝ (Space n) y)

lemma unitSegment_support {n : ℕ} (y x : Space n) : support (unitSegment y) x = |⟪x,y⟫| := by
  apply le_antisymm
  · apply (support_le_iff (unitSegment_compact y) (unitSegment_nonempty y)).mpr
    rintro _ ⟨a,ha,rfl⟩
    rw [real_inner_smul_right]
    calc
      _ ≤ |a*⟪x,y⟫| := le_abs_self _
      _ = |a| * |⟪x,y⟫| := abs_mul _ _
      _ ≤ 1 * |⟪x,y⟫| := mul_le_mul_of_nonneg_right (abs_le.mpr ha) (abs_nonneg _)
      _ = _ := one_mul _
  · rw [abs_le]
    constructor
    · have h := inner_le_support (unitSegment_compact y)
        (mem_image_of_mem (fun a : ℝ => a • y) (left_mem_Icc.mpr (by norm_num : (-1:ℝ) ≤ 1))) x
      simp only [real_inner_smul_right,neg_one_mul] at h
      linarith
    · have h := inner_le_support (unitSegment_compact y)
        (mem_image_of_mem (fun a : ℝ => a • y) (right_mem_Icc.mpr (by norm_num : (-1:ℝ) ≤ 1))) x
      simpa only [real_inner_smul_right,one_mul] using h

lemma smul_unitSegment {n : ℕ} (y : Space n) {t : ℝ} (ht : 0 ≤ t) :
    t • unitSegment y = (fun a : ℝ => a • y) '' Icc (-t) t := by
  have he : Icc (-t) t = (fun a : ℝ => t*a) '' Icc (-1) 1 := by
    simpa only [mul_neg,mul_one] using (image_mul_left_Icc ht (by norm_num : (-1:ℝ) ≤ 1)).symm
  rw [he,image_image,unitSegment,← image_smul,image_image]
  congr 1
  funext a
  exact smul_smul t a y

def shadowContinuousEquiv {n : ℕ} (u : Sphere n) :
    (perpendicular (u : Space n) × ℝ) ≃L[ℝ] Space n :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (perpendicular (u : Space n)) ℝ).symm.trans
    (shadowCoords u).toContinuousLinearEquiv

lemma shadowContinuousEquiv_apply {n : ℕ} (u : Sphere n) (z : perpendicular (u : Space n) × ℝ) :
    shadowContinuousEquiv u z = z.1+z.2 • (u : Space n) := rfl

lemma shadow_preimage_projection {n : ℕ} (u : Sphere n) (K : Set (Space n)) :
    Prod.fst '' (shadowContinuousEquiv u ⁻¹' K) =
      (perpendicular (u : Space n)).orthogonalProjectionOnto '' K := by
  ext z
  constructor
  · rintro ⟨⟨w,t⟩,hw,rfl⟩
    exact ⟨shadowContinuousEquiv u (w,t),hw,shadowCoords_projection u w t⟩
  · rintro ⟨x,hx,rfl⟩
    let q := (shadowContinuousEquiv u).symm x
    have hq : shadowContinuousEquiv u q = x := (shadowContinuousEquiv u).apply_symm_apply x
    refine ⟨q,?_,?_⟩
    · change shadowContinuousEquiv u q ∈ K
      rwa [hq]
    · rw [← hq]
      exact (shadowCoords_projection u q.1 q.2).symm

lemma shadow_preimage_add_segment {n : ℕ} (u : Sphere n) (K : Set (Space n))
    {t : ℝ} (ht : 0 ≤ t) :
    shadowContinuousEquiv u ⁻¹' (K+t • unitSegment (u : Space n)) =
      (shadowContinuousEquiv u ⁻¹' K) + Prod.mk 0 '' Icc (-t) t := by
  rw [smul_unitSegment _ ht]
  ext z
  constructor
  · rintro ⟨x,hx,_,⟨a,ha,rfl⟩,he⟩
    refine ⟨(shadowContinuousEquiv u).symm x,by simpa using hx,(0,a),⟨a,ha,rfl⟩,?_⟩
    apply (shadowContinuousEquiv u).injective
    rw [map_add,ContinuousLinearEquiv.apply_symm_apply,shadowContinuousEquiv_apply,Submodule.coe_zero,zero_add]
    exact he
  · rintro ⟨x,hx,_,⟨a,ha,rfl⟩,rfl⟩
    change shadowContinuousEquiv u (x+(0,a)) ∈ K+(fun a : ℝ => a • (u : Space n)) '' Icc (-t) t
    rw [map_add,shadowContinuousEquiv_apply u (0,a),Submodule.coe_zero,zero_add]
    exact add_mem_add hx (mem_image_of_mem _ ha)

/-- Adding a centered segment increases volume by its length times the actual
orthogonal shadow volume. No boundary regularity is used. -/
theorem segment_volume {n : ℕ} (u : Sphere n) {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) {t : ℝ} (ht : 0 ≤ t) :
    volume.real (K+t • unitSegment (u : Space n)) =
      volume.real K+2*t*shadowVolume K u := by
  let e := shadowContinuousEquiv u
  have hC : IsCompact (e ⁻¹' K) := e.toHomeomorph.isCompact_preimage.mpr hK
  have hcv : Convex ℝ (e ⁻¹' K) := hc.linear_preimage e.toLinearMap
  have h := vertical_segment_volume hC hcv ht
  rw [← shadow_preimage_add_segment u K ht,shadow_preimage_projection] at h
  have hm := shadowMeasurableEquiv_measurePreserving u
  have hm' (B : Set (Space n)) (hB : MeasurableSet B) : volume (e ⁻¹' B) = volume B :=
    hm.measure_preimage hB.nullMeasurableSet
  rw [hm' _ (hK.add ((unitSegment_compact _).smul t)).measurableSet,hm' _ hK.measurableSet] at h
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add hK.measure_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (hK.image (perpendicular (u : Space n)).orthogonalProjectionOnto.continuous).measure_ne_top),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)] at hr
  exact hr

/-- Gauge representation of actual orthogonal shadow volume. -/
theorem shadow_gauge_formula {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) (u : Sphere n) :
    2*shadowVolume K u = n*kappa n*mean (fun v : Sphere n =>
      (gauge K (v : Space n))⁻¹^n*|⟪∇ (gauge K) (v : Space n),(u : Space n)⟫|) := by
  have hd := minkowski_volume_derivative hK hc h0 (unitSegment_compact (u : Space n))
    (unitSegment_convex (u : Space n)) (unitSegment_nonempty (u : Space n))
  simp_rw [unitSegment_support] at hd
  have hlin : HasDerivAt (fun t : ℝ => volume.real K+2*t*shadowVolume K u)
      (2*shadowVolume K u) 0 := by
    apply (((hasDerivAt_id (0:ℝ)).const_mul (2:ℝ)).mul_const (shadowVolume K u)).const_add (volume.real K) |>.congr_deriv
    ring
  have hd' := hlin.hasDerivWithinAt (s := Ici (0:ℝ)) |>.congr
    (fun t ht => segment_volume u hK hc ht) (segment_volume u hK hc le_rfl)
  exact (hd'.derivWithin (uniqueDiffWithinAt_Ici (0:ℝ))).symm.trans
    (hd.derivWithin (uniqueDiffWithinAt_Ici (0:ℝ)))

end PettyProjection
end

end OAI
