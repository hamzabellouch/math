import OAI.Geometry.CylinderCovering.Angular.TableGeometryDefinitions
import OAI.Geometry.CylinderCovering.Convexity.CylinderSimilarity
import OAI.Geometry.TriangularCovering.Main

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace CylinderCovering.AngularTableGeometry

theorem area_dilate {r : ℝ} (hr : r ≠ 0) (S : Set Space) :
    TriangularCovering.area (dilate r S) = r^2 * TriangularCovering.area S := by
  have harea := Similarity.area_map (0 : Space) hr (LinearIsometryEquiv.refl ℝ Space) S
  unfold Similarity.map at harea
  simpa [Similarity.area, dilate, TriangularCovering.area] using harea

theorem shadowArea_body {r : ℝ} (hr : r ≠ 0) (u : Space) :
    CylinderCovering.shadowArea (body r) u = r^2 * TriangularCovering.shadowArea u := by
  have heq : TriangularCovering.projection u '' body r =
      dilate r (TriangularCovering.projection u '' TriangularCovering.K) := by
    simp only [body,dilate,image_image]
    congr 1
    funext x
    simp only [TriangularCovering.projection,inner_smul_right,smul_sub,smul_smul]
  unfold CylinderCovering.shadowArea TriangularCovering.shadowArea
  rw [heq,area_dilate hr]

theorem minimumShadowArea_body {r : ℝ} (hr : r ≠ 0) :
    minimumShadowArea (body r) = r^2 * TriangularCovering.H := by
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨TriangularCovering.tiltV 0 0 0,TriangularCovering.xAxis_unit,?_⟩
    rw [shadowArea_body hr,TriangularCovering.xAxis_shadow]
  · rintro a ⟨u,hu,rfl⟩
    rw [shadowArea_body hr]
    exact mul_le_mul_of_nonneg_left (TriangularCovering.shadowArea_ge_H hu) (sq_nonneg r)

theorem carrier_dilate_subset (r : ℝ) (u : Space) (B : Set Space) :
    dilate r (AngularGeneral.carrier u B) ⊆ AngularGeneral.carrier u (dilate r B) := by
  rintro z ⟨w,⟨b,hb,s,rfl⟩,rfl⟩
  refine ⟨r • b,⟨b,hb,rfl⟩,r*s,?_⟩
  module

theorem covers_dilate {τ : ℝ} {D : AngularGeneral.Data} (r : ℝ)
    (hc : AngularGeneral.covers τ D) : covers r τ D := by
  rintro z ⟨w,hw,rfl⟩
  obtain ⟨j,hj⟩ := hc w hw
  refine ⟨j,?_⟩
  rcases hj with hj | hj
  · exact Or.inl (carrier_dilate_subset r _ _ ⟨w,hj,rfl⟩)
  · exact Or.inr (carrier_dilate_subset r _ _ ⟨w,hj,rfl⟩)

theorem totalArea_dilate {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (D : AngularGeneral.Data) :
    totalArea r τ D = r^2 * AngularGeneral.totalArea τ D := by
  unfold totalArea AngularGeneral.totalArea lowerBase upperBase
  simp_rw [area_dilate hr]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem normalizedArea_dilate {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (D : AngularGeneral.Data) :
    totalArea r τ D / minimumShadowArea (body r) =
      AngularGeneral.totalArea τ D / TriangularCovering.H := by
  rw [totalArea_dilate hr,minimumShadowArea_body hr]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hr)

theorem relativeCost_dilate {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (D : AngularGeneral.Data) :
    relativeCost r τ D = AngularGeneral.relativeCost τ D := by
  unfold relativeCost AngularGeneral.relativeCost lowerBase upperBase
  simp_rw [area_dilate hr,shadowArea_body hr]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 hr),mul_div_mul_left _ _ (pow_ne_zero 2 hr)]

theorem dilate_eq_transportedBase (r : ℝ) (u : Space) (B : Set Space) :
    dilate r B = Similarity.transportedBase B u 0 r (LinearIsometryEquiv.refl ℝ Space) := by
  unfold dilate Similarity.transportedBase Similarity.baseMap
  simp [Similarity.project]

theorem baseProperties_dilate {r : ℝ} (hr : r ≠ 0) {u : Space} {B : Set Space}
    (hB : AngularGeneral.BaseProperties u B) :
    AngularGeneral.BaseProperties u (dilate r B) := by
  rcases hB with ⟨hu,hperp,hcompact,hmeas,hfinite⟩
  have hc : IsCompact (dilate r B) := hcompact.image (by fun_prop)
  refine ⟨hu,?_,hc,hc.measurableSet,?_⟩
  · rintro z ⟨x,hx,rfl⟩
    simp only [inner_smul_right,hperp x hx,mul_zero]
  · rw [dilate_eq_transportedBase r u B]
    exact Similarity.transportedBase_finite hfinite u 0 hr (LinearIsometryEquiv.refl ℝ Space)

theorem triangle_dilate {r : ℝ} (hr : r ≠ 0) {B : Set Space}
    (hB : AngularGeneral.IsNondegenerateTriangle B) :
    AngularGeneral.IsNondegenerateTriangle (dilate r B) := by
  rw [dilate_eq_transportedBase r (0 : Space) B]
  exact Similarity.transportedBase_triangular hB 0 0 hr (LinearIsometryEquiv.refl ℝ Space)

theorem conclusion_dilate {r τ η A : ℝ} {D : AngularGeneral.Data} (hr : r ≠ 0)
    (h : AngularGeneral.Conclusion τ η A D) : Conclusion r τ η A D := by
  rcases h with ⟨hcover,hbase,hexact,herror,hstrict,hrel,htri⟩
  refine ⟨covers_dilate r hcover,?_,?_,?_,?_,?_,?_⟩
  · intro j hj
    exact ⟨baseProperties_dilate hr (hbase j hj).1,
      baseProperties_dilate hr (hbase j hj).2⟩
  · rw [normalizedArea_dilate hr]
    exact hexact
  · rw [normalizedArea_dilate hr]
    exact herror
  · rw [totalArea_dilate hr,minimumShadowArea_body hr]
    have hstrict' : AngularGeneral.totalArea τ D < TriangularCovering.H/2 := by
      simpa only [TriangularCovering.projection_minimum] using hstrict
    have hmul := mul_lt_mul_of_pos_left hstrict' (sq_pos_of_ne_zero hr)
    nlinarith only [hmul]
  · rw [relativeCost_dilate hr]
    exact hrel
  · intro j hj hconstant
    exact ⟨triangle_dilate hr (htri j hj hconstant).1,
      triangle_dilate hr (htri j hj hconstant).2⟩

end CylinderCovering.AngularTableGeometry

end

end OAI
