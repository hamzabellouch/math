import OAI.Analysis.KadisonKastler.CompleteLinearOperations
import OAI.Analysis.KadisonKastler.RectangularCorner
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI

/-! Finite index changes for the rectangular matrix estimates used in row averaging. -/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Independent changes of row and column indices preserve the matrix norm. -/
theorem norm_reindex_rectangular {ι κ ι' κ' : Type*}
    [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    (e : ι ≃ ι') (d : κ ≃ κ') (X : CStarMatrix ι κ A) :
    ‖CStarMatrix.reindexₗ ℂ A e d X‖ = ‖X‖ := by
  classical
  have he : rectangularCorner (CStarMatrix.reindexₗ ℂ A e d X) =
      CStarMatrix.reindexₐ ℂ A (Equiv.sumCongr e d) (rectangularCorner X) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  calc
    _ = ‖rectangularCorner (CStarMatrix.reindexₗ ℂ A e d X)‖ :=
      (norm_rectangularCorner _).symm
    _ = ‖CStarMatrix.reindexₐ ℂ A (Equiv.sumCongr e d) (rectangularCorner X)‖ :=
      congrArg norm he
    _ = ‖rectangularCorner X‖ := NonUnitalStarAlgHom.norm_map
      (CStarMatrix.reindexₐ ℂ A (Equiv.sumCongr e d)).toStarAlgHom
      (CStarMatrix.reindexₐ ℂ A (Equiv.sumCongr e d)).injective _
    _ = ‖X‖ := norm_rectangularCorner X

/-- Complete bounds apply to arbitrary finite square index types. -/
theorem CompletelyBoundedBy.finite_square {F : A →ₗ[ℂ] B} {c : ℝ}
    (hF : CompletelyBoundedBy F c) {ι : Type*} [Fintype ι]
    (X : CStarMatrix ι ι A) : ‖CStarMatrix.mapₗ F X‖ ≤ c * ‖X‖ := by
  classical
  let e := Fintype.equivFin ι
  let eA := CStarMatrix.reindexₐ ℂ A e
  let eB := CStarMatrix.reindexₐ ℂ B e
  have h := hF (Fintype.card ι) (Fintype.card ι) (eA X)
  have he : CStarMatrix.mapₗ F (eA X) = eB (CStarMatrix.mapₗ F X) := rfl
  have hA : ‖eA X‖ = ‖X‖ := NonUnitalStarAlgHom.norm_map eA.toStarAlgHom eA.injective X
  have hB : ‖eB (CStarMatrix.mapₗ F X)‖ = ‖CStarMatrix.mapₗ F X‖ :=
    NonUnitalStarAlgHom.norm_map eB.toStarAlgHom eB.injective _
  rwa [he, hA, hB] at h

/-- Complete bounds apply to arbitrary finite rectangular index types. -/
theorem CompletelyBoundedBy.finite {F : A →ₗ[ℂ] B} {c : ℝ}
    (hF : CompletelyBoundedBy F c) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : CStarMatrix ι κ A) : ‖CStarMatrix.mapₗ F X‖ ≤ c * ‖X‖ := by
  have h := hF.finite_square (rectangularCorner X)
  rwa [← rectangularCorner_map, norm_rectangularCorner, norm_rectangularCorner] at h

omit [PartialOrder A] [StarOrderedRing A] in
theorem rectangular_toCLM_mul_finite {ι κ τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ]
    (X : CStarMatrix ι κ A) (Y : CStarMatrix κ τ A) :
    CStarMatrix.toCLM (X * Y) = (CStarMatrix.toCLM Y).comp (CStarMatrix.toCLM X) := by
  ext v i
  simp only [CStarMatrix.toCLM_apply, ContinuousLinearMap.comp_apply]
  exact congrFun (Matrix.vecMul_vecMul v X Y).symm i

theorem rectangular_norm_mul_le_finite {ι κ τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ]
    (X : CStarMatrix ι κ A) (Y : CStarMatrix κ τ A) :
    ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ := by
  simp only [CStarMatrix.norm_def, rectangular_toCLM_mul_finite]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

end

end KadisonKastler

end OAI
