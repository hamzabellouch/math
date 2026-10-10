import OAI.Geometry.NodalSets.Charts.SphereCotangentCoordinates
import OAI.Geometry.NodalSets.Elliptic.IntrinsicAmbientSmooth

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped RealInnerProductSpace
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

def sphereCoordinateCovector (p : Base) (z : BaseModel) (v : Fin 4 → ℝ) :
    SphereCotangent ((extChartAt (𝓡 4) p).symm z) :=
  sphereCovectorRestriction _ (WithLp.toLp 2 ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ v))

lemma sphereCoordinateCovector_apply (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (v w : Fin 4 → ℝ) :
    sphereCoordinateCovector p z v
      (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm z (WithLp.toLp 2 w)) =
      v ⬝ᵥ w := by
  change ⟪WithLp.toLp 2 ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ v),
    sphereChartDerivative p z (WithLp.toLp 2 w)⟫ = _
  have he : ∀ u t : AmbientBase, ⟪u,t⟫ = (⇑u) ⬝ᵥ ⇑t := by
    intro u t
    simp [PiLp.inner_apply,dotProduct,mul_comm]
  rw [he]
  change ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ v) ⬝ᵥ
    (fun i ↦ sphereChartDerivative p z (WithLp.toLp 2 w) i) = _
  rw [← sphereChartFrame_mulVec, dotProduct_mulVec, ← mulVec_transpose,
    sphereChart_covector_representative p hz]

lemma sphereCoordinateCovector_unique (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (v : Fin 4 → ℝ)
    (ell : SphereCotangent ((extChartAt (𝓡 4) p).symm z))
    (hell : ∀ w : Fin 4 → ℝ, ell
      (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm z (WithLp.toLp 2 w)) = v ⬝ᵥ w) :
    ell = sphereCoordinateCovector p z v := by
  have hs := (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 4) hz).surjective
  rw [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at hs
  ext u
  obtain ⟨w,rfl⟩ := hs u
  exact (hell (WithLp.ofLp w)).trans (sphereCoordinateCovector_apply p hz v (WithLp.ofLp w)).symm

lemma sphereChart_representative_radial (p : Base) (z : BaseModel) (v : Fin 4 → ℝ) :
    ⟪((extChartAt (𝓡 4) p).symm z : AmbientBase),
      WithLp.toLp 2 ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ v)⟫ = 0 := by
  have he : ∀ u t : AmbientBase, ⟪u,t⟫ = (⇑u) ⬝ᵥ ⇑t := by
    intro u t
    simp [PiLp.inner_apply,dotProduct,mul_comm]
  rw [he, dotProduct_mulVec, ← mulVec_transpose, transpose_transpose,
    frameLeftInverse, ← mulVec_mulVec, sphereChartFrame_orthogonal, mulVec_zero, zero_dotProduct]

lemma intrinsicAmbientMatrix_chart_pairing (A : IntrinsicTensor)
    (p : Base) (z : BaseModel) (v w : Fin 4 → ℝ) :
    v ⬝ᵥ (sphereChartTensor (intrinsicAmbientMatrix A) p z *ᵥ w) =
      A ((extChartAt (𝓡 4) p).symm z)
        (sphereCoordinateCovector p z v) (sphereCoordinateCovector p z w) := by
  rw [sphereChartTensor_pairing]
  have h := intrinsicAmbientMatrix_tangent A ((extChartAt (𝓡 4) p).symm z)
    (WithLp.toLp 2 ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ v))
    (WithLp.toLp 2 ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ w))
    (sphereChart_representative_radial p z v)
  rw [ambientMatrixForm_dot] at h
  convert h using 1
  rfl

def intrinsicSphereChartTensor (A : IntrinsicTensor) (p : Base) (z : BaseModel) :
    Matrix (Fin 4) (Fin 4) ℝ := fun i j ↦
  A ((extChartAt (𝓡 4) p).symm z)
    (sphereCoordinateCovector p z (Pi.single i 1))
    (sphereCoordinateCovector p z (Pi.single j 1))

lemma intrinsicSphereChartTensor_eq (A : IntrinsicTensor) (p : Base) (z : BaseModel) :
    intrinsicSphereChartTensor A p z = sphereChartTensor (intrinsicAmbientMatrix A) p z := by
  ext i j
  have h := intrinsicAmbientMatrix_chart_pairing A p z (Pi.single i 1) (Pi.single j 1)
  simpa [intrinsicSphereChartTensor] using h.symm

end
end Yau.Target

end OAI
