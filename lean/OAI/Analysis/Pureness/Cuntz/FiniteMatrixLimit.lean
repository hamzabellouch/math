import OAI.Analysis.Pureness.Operators.FiniteCorners
import Mathlib.Algebra.Colimit.DirectLimit

namespace OAI
namespace CuntzPureness
variable (A : Type*) [CStarAlgebra A]

abbrev MatrixStage (k : ℕ) := CStarMatrix (Fin k) (Fin k) A
noncomputable def matrixConnecting (k l : ℕ) (h : k ≤ l) :
    MatrixStage A k →⋆ₙₐ[ℂ] MatrixStage A l := cornerHom h

instance matrixDirectedSystem : DirectedSystem (MatrixStage A) (fun _ _ h => matrixConnecting A _ _ h) where
  map_self := by intro i x; exact corner_refl x
  map_map := by intro k j i h g a; exact corner_comp h g a

abbrev FiniteMatrixLimit := DirectLimit (MatrixStage A) (matrixConnecting A)

noncomputable def finiteMatrixInclude (k : ℕ) : MatrixStage A k →⋆ₙₐ[ℂ] FiniteMatrixLimit A where
  toFun a := Quotient.mk _ ⟨k, a⟩
  map_zero' := (DirectLimit.zero_def k).symm
  map_add' a b := (DirectLimit.add_def k a b).symm
  map_mul' a b := (DirectLimit.mul_def k a b).symm
  map_smul' z a := (DirectLimit.smul_def k a z).symm
  map_star' a := (DirectLimit.star_def k a).symm

lemma finiteMatrixInclude_injective (k : ℕ) : Function.Injective (finiteMatrixInclude A k) :=
  DirectLimit.mk_injective (matrixConnecting A) (fun _ _ h => corner_injective h) k

lemma finiteMatrixInclude_corner {k l : ℕ} (h : k ≤ l) (a : MatrixStage A k) :
    finiteMatrixInclude A l (corner h a) = finiteMatrixInclude A k a :=
  (DirectLimit.eq_of_le ⟨k, a⟩ l h).symm

variable [PartialOrder A] [StarOrderedRing A]

noncomputable def finiteMatrixNorm : FiniteMatrixLimit A → ℝ :=
  DirectLimit.lift (matrixConnecting A) (fun _ a => ‖a‖)
    (fun _ _ h a => (corner_norm h a).symm)

@[simp] lemma finiteMatrixNorm_include (k : ℕ) (a : MatrixStage A k) :
    finiteMatrixNorm A (finiteMatrixInclude A k a) = ‖a‖ := rfl

noncomputable def finiteMatrixGroupNorm : AddGroupNorm (FiniteMatrixLimit A) where
  toFun := finiteMatrixNorm A
  map_zero' := by rw [← map_zero (finiteMatrixInclude A 0), finiteMatrixNorm_include, norm_zero]
  add_le' := by
    apply DirectLimit.induction₂
    intro k a b
    change finiteMatrixNorm A (finiteMatrixInclude A k a + finiteMatrixInclude A k b) ≤ _
    rw [← map_add, finiteMatrixNorm_include]
    exact norm_add_le a b
  neg' := by
    apply DirectLimit.induction
    intro k a
    change finiteMatrixNorm A (-finiteMatrixInclude A k a) = _
    rw [← map_neg, finiteMatrixNorm_include]
    exact norm_neg a
  eq_zero_of_map_eq_zero' := by
    apply DirectLimit.induction
    intro k a ha
    have hz : a = 0 := norm_eq_zero.mp ha
    change finiteMatrixInclude A k a = 0
    rw [hz, map_zero]

noncomputable instance finiteMatrixNormedAddCommGroup : NormedAddCommGroup (FiniteMatrixLimit A) :=
  (finiteMatrixGroupNorm A).toNormedAddCommGroup

noncomputable instance finiteMatrixTopology : TopologicalSpace (FiniteMatrixLimit A) :=
  (finiteMatrixNormedAddCommGroup A).toMetricSpace.toUniformSpace.toTopologicalSpace

@[simp] lemma finiteMatrixInclude_norm (k : ℕ) (a : MatrixStage A k) :
    ‖finiteMatrixInclude A k a‖ = ‖a‖ := rfl

lemma finiteMatrixInclude_isometry (k : ℕ) : Isometry (finiteMatrixInclude A k) :=
  AddMonoidHomClass.isometry_of_norm _ (finiteMatrixInclude_norm A k)

noncomputable instance finiteMatrixNonUnitalNormedRing : NonUnitalNormedRing (FiniteMatrixLimit A) where
  dist_eq x y := by rw [dist_eq_norm, ← norm_neg]; simp [sub_eq_add_neg, add_comm]
  norm_mul_le := by
    apply DirectLimit.induction₂
    intro k a b
    change ‖finiteMatrixInclude A k a * finiteMatrixInclude A k b‖ ≤ _
    rw [← map_mul, finiteMatrixInclude_norm]
    exact norm_mul_le a b

noncomputable instance finiteMatrixModule : Module ℂ (FiniteMatrixLimit A) where
  one_smul := by
    apply DirectLimit.induction
    intro k a
    simp only [one_smul]
  mul_smul r s := by
    apply DirectLimit.induction
    intro k a
    simp only [DirectLimit.smul_def, mul_smul]
  smul_zero r := by
    rw [DirectLimit.zero_def 0, DirectLimit.smul_def, smul_zero]
  smul_add r := by
    apply DirectLimit.induction₂
    intro k a b
    simp only [DirectLimit.smul_def, DirectLimit.add_def, smul_add]
  add_smul r s := by
    apply DirectLimit.induction
    intro k a
    simp only [DirectLimit.smul_def, DirectLimit.add_def, add_smul]
  zero_smul := by
    apply DirectLimit.induction
    intro k a
    simp only [DirectLimit.smul_def, zero_smul, DirectLimit.zero_def k]

noncomputable instance finiteMatrixNormedSpace : NormedSpace ℂ (FiniteMatrixLimit A) where
  __ : Module ℂ (FiniteMatrixLimit A) := inferInstance
  norm_smul_le z := by
    apply DirectLimit.induction
    intro k a
    change ‖z • finiteMatrixInclude A k a‖ ≤ ‖z‖ * ‖finiteMatrixInclude A k a‖
    rw [← map_smul, finiteMatrixInclude_norm, finiteMatrixInclude_norm]
    exact norm_smul_le z a

noncomputable instance finiteMatrixStarRing : StarRing (FiniteMatrixLimit A) where
  __ : StarAddMonoid (FiniteMatrixLimit A) := inferInstance
  __ : StarMul (FiniteMatrixLimit A) := inferInstance

instance finiteMatrixCStarRing : CStarRing (FiniteMatrixLimit A) where
  norm_mul_self_le := by
    apply DirectLimit.induction
    intro k a
    change ‖finiteMatrixInclude A k a‖ * ‖finiteMatrixInclude A k a‖ ≤
      ‖star (finiteMatrixInclude A k a) * finiteMatrixInclude A k a‖
    rw [← map_star, ← map_mul, finiteMatrixInclude_norm, finiteMatrixInclude_norm]
    exact CStarRing.norm_mul_self_le a
end CuntzPureness

end OAI
