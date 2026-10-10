import OAI.Analysis.Pureness.Stabilization.MatrixBlock

namespace OAI
noncomputable section
open scoped Topology CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma matrixBlockHom_stage (n : ℕ) (P : FinMatrix A n × FinMatrix A n) :
    matrixBlockHom (matrixLimitStage n P.1,matrixLimitStage n P.2) = matrixLimitBlock n P := by
  change matrixEven (matrixLimitStage n P.1) + matrixOdd (matrixLimitStage n P.2) = _
  rw [matrixEven_stage,matrixOdd_stage,← map_add]
  congr 1
  simp

private lemma starHom_continuous {D B : Type*} [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra B]
    (f : D →⋆ₙₐ[ℂ] B) : Continuous f := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simpa only [dist_eq_norm,← map_sub,NNReal.coe_one,one_mul] using
    NonUnitalStarAlgHom.norm_apply_le f (a-b)

theorem matrixBlockHom_norm (x y : MatrixLimit A) : ‖matrixBlockHom (x,y)‖ = max ‖x‖ ‖y‖ := by
  refine finiteMatrixSubalgebra_dense.induction_on₂ ?_ ?_ x y
  · exact isClosed_eq (starHom_continuous matrixBlockHom).norm
      ((continuous_fst.norm).max continuous_snd.norm)
  · intro u v
    obtain ⟨n,M,N,hu,hv⟩ := finiteMatrix_common_stage u v
    rw [← hu,← hv]
    change ‖matrixBlockHom (matrixLimitStage n M,matrixLimitStage n N)‖ =
      max ‖matrixLimitStage n M‖ ‖matrixLimitStage n N‖
    rw [matrixBlockHom_stage n (M,N),matrixLimitBlock_norm,matrixLimitStage_norm,matrixLimitStage_norm]

theorem matrixBlockHom_isometry : Isometry (matrixBlockHom (A := A)) :=
  AddMonoidHomClass.isometry_of_norm _ (fun P => matrixBlockHom_norm P.1 P.2)
end CuntzTrace

end

end OAI
