import OAI.Analysis.Pureness.Operators.DenseSchurNorm
import OAI.Analysis.Pureness.Tensor.SpatialHilbertBasisDensity

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct InnerProductSpace
local instance spatialSchurNormDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
variable {H V G : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]

lemma spatial_compression_inner (T : SpatialHilbert H (GroupL2 G) →L[ℂ] SpatialHilbert H (GroupL2 G))
    (a b : H) (g h : G) :
    ⟪a, (spatialRightVector (H := H) (lp.single 2 g (1 : ℂ))).adjoint.comp
      (T.comp (spatialRightVector (lp.single 2 h (1 : ℂ)))) b⟫_ℂ =
    ⟪((a ⊗ₜ[ℂ] (lp.single 2 g (1 : ℂ)) : H ⊗[ℂ] GroupL2 G) : SpatialHilbert H (GroupL2 G)),
      T (b ⊗ₜ[ℂ] (lp.single 2 h (1 : ℂ)) : H ⊗[ℂ] GroupL2 G)⟫_ℂ := by
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem spatialSchur_norm_le (v w : G → V) (hv : ∀ g, ‖v g‖ ≤ 1) (hw : ∀ g, ‖w g‖ ≤ 1)
    (S T : SpatialHilbert H (GroupL2 G) →L[ℂ] SpatialHilbert H (GroupL2 G))
    (hentry : ∀ g h,
      (spatialRightVector (H := H) (lp.single 2 g (1 : ℂ))).adjoint.comp
        (S.comp (spatialRightVector (lp.single 2 h (1 : ℂ)))) =
      ⟪v g, w h⟫_ℂ •
        (spatialRightVector (H := H) (lp.single 2 g (1 : ℂ))).adjoint.comp
          (T.comp (spatialRightVector (lp.single 2 h (1 : ℂ))))) : ‖S‖ ≤ ‖T‖ := by
  obtain ⟨I, b, hb⟩ := exists_hilbertBasis ℂ H
  let e := fun p : I × G =>
    ((b p.1 ⊗ₜ[ℂ] (lp.single 2 p.2 (1 : ℂ)) : H ⊗[ℂ] GroupL2 G) : SpatialHilbert H (GroupL2 G))
  apply schur_norm_le_of_dense_orthonormal (E := SpatialHilbert H (GroupL2 G))
    (V := V) (ι := I × G) e
    (spatialTensorFamily_orthonormal b (fun g : G => (lp.single 2 g 1 : GroupL2 G)) b.orthonormal (groupDelta_orthonormal G))
    (spatialTensorFamily_dense b (fun g : G => (lp.single 2 g 1 : GroupL2 G)) (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span) (groupDelta_dense G))
    (fun p => v p.2) (fun p => w p.2) (fun p => hv p.2) (fun p => hw p.2) S T
  intro i j
  have hc := congrArg (fun U : H →L[ℂ] H => ⟪b i.1, U (b j.1)⟫_ℂ) (hentry i.2 j.2)
  simp only [smul_apply, inner_smul_right] at hc
  exact (spatial_compression_inner S (b i.1) (b j.1) i.2 j.2).symm.trans
    (hc.trans ((congrArg (fun z : ℂ => ⟪v i.2, w j.2⟫_ℂ * z)
      (spatial_compression_inner T (b i.1) (b j.1) i.2 j.2)).trans (mul_comm _ _)))
end CuntzPureness

end

end OAI
