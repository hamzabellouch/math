import OAI.Geometry.NodalSets.Charts.SphereCovectorRestriction
import OAI.Geometry.NodalSets.Elliptic.AmbientFormMatrix

namespace OAI

namespace Yau.Target
open Bundle Manifold ContinuousLinearMap Matrix
open scoped ContDiff RealInnerProductSpace
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

abbrev IntrinsicTensor := ∀ x : Base, SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ

def intrinsicAmbientForm (A : IntrinsicTensor) (x : Base) :
    AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ :=
  ((sphereCovectorRestriction x).precomp ℝ).comp ((A x).comp (sphereCovectorRestriction x)) +
    (innerSL ℝ (x : AmbientBase)).smulRight (innerSL ℝ (x : AmbientBase))

def intrinsicAmbientMatrix (A : IntrinsicTensor) (x : Base) : Matrix (Fin 5) (Fin 5) ℝ :=
  ambientFormMatrix (intrinsicAmbientForm A x)

lemma intrinsicAmbientForm_apply (A : IntrinsicTensor) (x : Base) (v w : AmbientBase) :
    intrinsicAmbientForm A x v w =
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) +
        ⟪(x : AmbientBase),v⟫ * ⟪(x : AmbientBase),w⟫ := rfl

lemma intrinsicAmbientMatrix_pairing (A : IntrinsicTensor) (x : Base) (v w : AmbientBase) :
    ambientMatrixForm (intrinsicAmbientMatrix A x) v w =
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) +
        ⟪(x : AmbientBase),v⟫ * ⟪(x : AmbientBase),w⟫ := by
  rw [intrinsicAmbientMatrix, ambientFormMatrix_form, intrinsicAmbientForm_apply]

lemma intrinsicAmbientMatrix_tangent (A : IntrinsicTensor) (x : Base) (v w : AmbientBase)
    (hv : ⟪(x : AmbientBase),v⟫ = 0) :
    ambientMatrixForm (intrinsicAmbientMatrix A x) v w =
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) := by
  rw [intrinsicAmbientMatrix_pairing,hv,zero_mul,add_zero]

lemma intrinsicAmbientMatrix_posDef (A : IntrinsicTensor)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (x : Base) :
    (intrinsicAmbientMatrix A x).PosDef := by
  apply ambientFormMatrix_posDef
  · intro v w
    simp only [intrinsicAmbientForm_apply, mul_comm]
    rw [hs]
  · intro v hv
    rw [intrinsicAmbientForm_apply]
    by_cases hz : sphereCovectorRestriction x v = 0
    · have hn : ⟪(x : AmbientBase),v⟫ ≠ 0 := by
        intro h
        exact hv (sphereCovectorRestriction_separates x v hz h)
      rw [hz, map_zero (A x 0), zero_add]
      exact mul_self_pos.mpr hn
    · exact add_pos_of_pos_of_nonneg (hp x _ hz) (mul_self_nonneg _)

lemma intrinsicAmbientMatrix_radial (A : IntrinsicTensor) (x : Base) :
    intrinsicAmbientMatrix A x *ᵥ (fun i ↦ (x : AmbientBase) i) =
      (fun i ↦ (x : AmbientBase) i) := by
  have hx : ⟪(x : AmbientBase),(x : AmbientBase)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have hn : ‖(x : AmbientBase)‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using x.property
    rw [hn,one_pow]
  ext i
  have h := intrinsicAmbientMatrix_pairing A x (EuclideanSpace.basisFun (Fin 5) ℝ i)
    (x : AmbientBase)
  rw [sphereCovectorRestriction_radial,map_zero,hx,mul_one,zero_add] at h
  simpa [ambientMatrixForm_dot,dotProduct,EuclideanSpace.basisFun_inner,
    EuclideanSpace.inner_single_right] using h

end
end Yau.Target

end OAI
