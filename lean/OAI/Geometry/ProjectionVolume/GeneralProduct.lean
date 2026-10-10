import OAI.Geometry.ProjectionVolume.ProductArea
import OAI.Geometry.ProjectionVolume.ProductReconstruction
import OAI.Geometry.ProjectionVolume.PolytopeCauchy

namespace OAI

universe uι uκ

noncomputable section
open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace Pointwise

namespace Paper092

namespace HPolytope

variable {r s : ℕ} {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]

theorem product_faceArea_inl (hr : 0 < r) (A : HPolytope r ι) (B : HPolytope s κ)
    (i : ι) : (A.product B).faceArea (.inl i) =
      A.faceArea i * (volume B.body).toReal := by
  unfold faceArea
  rw [product_face_inl, cartesianBody_eq_preimage,
    affineHyperplane_product_area_left hr (A.normal i) (A.normal_unit i) (A.offset i)
      (A.face i) (A.face_isCompact i) (fun _ hx => hx.2) B.body B.compact.measurableSet,
    ENNReal.toReal_mul]

theorem product_faceArea_inr (hs : 0 < s) (A : HPolytope r ι) (B : HPolytope s κ)
    (i : κ) : (A.product B).faceArea (.inr i) =
      (volume A.body).toReal * B.faceArea i := by
  unfold faceArea
  rw [product_face_inr, cartesianBody_eq_preimage,
    affineHyperplane_product_area_right hs (B.normal i) (B.normal_unit i) (B.offset i)
      (B.face i) (B.face_isCompact i) (fun _ hx => hx.2) A.body A.compact.measurableSet,
    ENNReal.toReal_mul]

theorem brightness_product (hr : 0 < r) (hs : 0 < s)
    (A : HPolytope r ι) (B : HPolytope s κ) (w : Euclidean (r + s)) :
    brightness (cartesianBody A.body B.body) w =
      (volume B.body).toReal * brightness A.body (splitEuclideanProduct r s w).1 +
      (volume A.body).toReal * brightness B.body (splitEuclideanProduct r s w).2 := by
  classical
  rw [← product_body A B, (A.product B).brightness_eq_sum,
    A.brightness_eq_sum, B.brightness_eq_sum, Fintype.sum_sum_type]
  have hleft (i : ι) : ⟪w, (A.product B).normal (.inl i)⟫ =
      ⟪(splitEuclideanProduct r s w).1, A.normal i⟫ := by
    change ⟪w, productLiftLeft r s (A.normal i)⟫ = _
    rw [real_inner_comm, inner_productLiftLeft, real_inner_comm]
  have hright (i : κ) : ⟪w, (A.product B).normal (.inr i)⟫ =
      ⟪(splitEuclideanProduct r s w).2, B.normal i⟫ := by
    change ⟪w, productLiftRight r s (B.normal i)⟫ = _
    rw [real_inner_comm, inner_productLiftRight, real_inner_comm]
  simp_rw [product_faceArea_inl hr, product_faceArea_inr hs, hleft, hright]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have heq : (∑ i, A.faceArea i * ((volume B.body).toReal *
      |⟪(splitEuclideanProduct r s w).1, A.normal i⟫|)) =
      (volume B.body).toReal * ∑ i, A.faceArea i *
        |⟪(splitEuclideanProduct r s w).1, A.normal i⟫| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  ring

end HPolytope

theorem projectionBody_product {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] (A : HPolytope r ι) (B : HPolytope s κ) :
    projectionBody (cartesianBody A.body B.body) =
      cartesianBody ((volume B.body).toReal • projectionBody A.body)
        ((volume A.body).toReal • projectionBody B.body) :=
  projectionBody_cartesian_of_brightness A.body B.body A.volume_pos B.volume_pos
    (A.brightness_product (by omega) (by omega) B)

theorem normalizedProjectionVolume_product {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] (A : HPolytope r ι) (B : HPolytope s κ) :
    normalizedProjectionVolume (cartesianBody A.body B.body) =
      normalizedProjectionVolume A.body * normalizedProjectionVolume B.body :=
  normalized_cartesian_of_projectionBody_eq (by omega) (by omega) A.body B.body
    A.compact B.compact A.volume_pos B.volume_pos (projectionBody_product hr hs A B)

end Paper092

end

end OAI
