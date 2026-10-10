import OAI.Geometry.ProjectionVolume.FacetLinearImage
import OAI.Geometry.ProjectionVolume.GeneralProduct
import OAI.Geometry.ProjectionVolume.SimplexPolytope

namespace OAI

universe uι uκ

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Paper092

theorem affineHyperplane_linearImage_areaNormal {n : ℕ}
    (L : Euclidean n ≃ₗ[ℝ] Euclidean n) (v : Euclidean n) (hv : ‖v‖ = 1)
    (c : ℝ) (F : Set (Euclidean n)) (hplane : ∀ x ∈ F, ⟪v, x⟫ = c) :
    (μHE[n - 1] (L '' F)).toReal • linearImageNormal L v =
      (|L.toLinearMap.det| • L.symm.toLinearMap.adjoint) ((μHE[n - 1] F).toReal • v) := by
  rw [affineHyperplane_linearImage_area_real L v hv c F hplane, linearImageNormal,
    smul_smul, LinearMap.smul_apply, map_smul, smul_smul]
  congr 1
  field_simp [norm_ne_zero_iff.mpr (inverseAdjoint_ne_zero L v hv)]

theorem simplexFacet_coordinate_areaNormal (n : ℕ) (i : Fin (n + 1)) :
    (μHE[n] (simplexFacet (n + 1) (some i))).toReal •
        (-EuclideanSpace.single i (1 : ℝ)) =
      -(1 / (n.factorial : ℝ)) • EuclideanSpace.single i (1 : ℝ) := by
  rw [simplexFacet_coordinate_area, ENNReal.toReal_ofReal (by positivity)]
  exact (smul_neg _ _).trans (neg_smul _ _).symm

theorem simplexFacet_diagonal_areaNormal (n : ℕ) :
    (μHE[n] (simplexFacet (n + 1) none)).toReal • diagonalUnitNormal (n + 1) =
      (1 / (n.factorial : ℝ)) • diagonalVector (n + 1) := by
  rw [simplexFacet_diagonal_area, ENNReal.toReal_ofReal (by positivity),
    diagonalUnitNormal, smul_smul]
  congr 1
  have hs : Real.sqrt ((n : ℝ) + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  push_cast
  field_simp

namespace HPolytope

theorem product_areaNormal_inl {r s : ℕ} (hr : 0 < r)
    {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] (A : HPolytope r ι) (B : HPolytope s κ)
    (i : ι) :
    splitEuclideanProduct r s ((A.product B).faceArea (.inl i) •
        (A.product B).normal (.inl i)) =
      ((volume B.body).toReal • (A.faceArea i • A.normal i), 0) := by
  rw [product_faceArea_inl hr]
  change splitEuclideanProduct r s ((A.faceArea i * (volume B.body).toReal) •
    productLiftLeft r s (A.normal i)) = _
  simp [productLiftLeft, smul_smul, mul_comm]

theorem product_areaNormal_inr {r s : ℕ} (hs : 0 < s)
    {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] (A : HPolytope r ι) (B : HPolytope s κ)
    (i : κ) :
    splitEuclideanProduct r s ((A.product B).faceArea (.inr i) •
        (A.product B).normal (.inr i)) =
      (0, (volume A.body).toReal • (B.faceArea i • B.normal i)) := by
  rw [product_faceArea_inr hs]
  change splitEuclideanProduct r s (((volume A.body).toReal * B.faceArea i) •
    productLiftRight r s (B.normal i)) = _
  simp [productLiftRight, smul_smul]

end HPolytope
end Paper092

end

end OAI
