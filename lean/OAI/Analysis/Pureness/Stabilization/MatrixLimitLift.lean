import OAI.Analysis.Pureness.Stabilization.MatrixLimit
import OAI.Analysis.Pureness.Stabilization.DenseStarExtension

namespace OAI
noncomputable section
open scoped Topology CStarAlgebra
namespace CuntzTrace
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B]

def finiteMatrixSubalgebra : NonUnitalStarSubalgebra ℂ (MatrixLimit A) :=
  (matrixUnion A).comap (NonUnitalStarSubalgebraClass.subtype (matrixLimitAlgebra A))

def finiteMatrixStage (n : ℕ) (M : FinMatrix A n) : finiteMatrixSubalgebra (A := A) :=
  ⟨matrixLimitStage n M,⟨n,M,rfl⟩⟩

lemma finiteMatrixStage_surjective (x : finiteMatrixSubalgebra (A := A)) :
    ∃ (n : ℕ) (M : FinMatrix A n), finiteMatrixStage n M = x := by
  obtain ⟨n,M,hM⟩ := x.2
  exact ⟨n,M,Subtype.ext (Subtype.ext hM)⟩

lemma finiteMatrixSubalgebra_dense : DenseRange (fun x : finiteMatrixSubalgebra (A := A) => (x : MatrixLimit A)) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n,M,hM⟩ := matrixLimit_finite_approximation x hε
  exact ⟨matrixLimitStage n M,⟨finiteMatrixStage n M,rfl⟩,by simpa only [dist_eq_norm] using hM⟩

def finiteMatrixRepresentative (x : finiteMatrixSubalgebra (A := A)) : Σ n, FinMatrix A n :=
  ⟨(finiteMatrixStage_surjective x).choose,(finiteMatrixStage_surjective x).choose_spec.choose⟩

lemma finiteMatrixRepresentative_spec (x : finiteMatrixSubalgebra (A := A)) :
    finiteMatrixStage (finiteMatrixRepresentative x).1 (finiteMatrixRepresentative x).2 = x :=
  (finiteMatrixStage_surjective x).choose_spec.choose_spec

variable (f : ∀ n, FinMatrix A n →⋆ₙₐ[ℂ] B)
variable (hf : ∀ {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n), f m (matrixInclusion h M) = f n M)

def finiteMatrixLiftValue (x : finiteMatrixSubalgebra (A := A)) : B :=
  f (finiteMatrixRepresentative x).1 (finiteMatrixRepresentative x).2

include hf in
lemma finiteMatrixLiftValue_eq (x : finiteMatrixSubalgebra (A := A)) (n : ℕ) (M : FinMatrix A n)
    (hx : finiteMatrixStage n M = x) : finiteMatrixLiftValue f x = f n M := by
  let r := finiteMatrixRepresentative x
  have he : matrixLimitStage r.1 r.2 = matrixLimitStage n M :=
    congrArg Subtype.val ((finiteMatrixRepresentative_spec x).trans hx.symm)
  have hm : matrixInclusion (le_max_left r.1 n) r.2 = matrixInclusion (le_max_right r.1 n) M := by
    apply (matrixLimitStage_isometry (max r.1 n)).injective
    simpa only [matrixLimitStage_compatible] using he
  change f r.1 r.2 = f n M
  rw [← hf (le_max_left r.1 n) r.2,← hf (le_max_right r.1 n) M,hm]

include hf in
@[simp] lemma finiteMatrixLiftValue_stage (n : ℕ) (M : FinMatrix A n) :
    finiteMatrixLiftValue f (finiteMatrixStage n M) = f n M :=
  finiteMatrixLiftValue_eq f hf _ n M rfl

lemma finiteMatrix_common_stage (x y : finiteMatrixSubalgebra (A := A)) :
    ∃ (n : ℕ) (M N : FinMatrix A n), finiteMatrixStage n M = x ∧ finiteMatrixStage n N = y := by
  obtain ⟨n,M,rfl⟩ := finiteMatrixStage_surjective x
  obtain ⟨m,N,rfl⟩ := finiteMatrixStage_surjective y
  refine ⟨max n m,matrixInclusion (le_max_left n m) M,matrixInclusion (le_max_right n m) N,?_,?_⟩
  · exact Subtype.ext (matrixLimitStage_compatible _ _)
  · exact Subtype.ext (matrixLimitStage_compatible _ _)

def finiteMatrixLift : finiteMatrixSubalgebra (A := A) →⋆ₙₐ[ℂ] B where
  toFun := finiteMatrixLiftValue f
  map_zero' := by
    have hz : finiteMatrixStage (A := A) 0 0 = 0 := Subtype.ext (map_zero _)
    rw [← hz,finiteMatrixLiftValue_stage f hf,map_zero]
  map_add' x y := by
    obtain ⟨n,M,N,rfl,rfl⟩ := finiteMatrix_common_stage x y
    have he : finiteMatrixStage n (M+N) = finiteMatrixStage n M + finiteMatrixStage n N := Subtype.ext (map_add _ _ _)
    rw [← he,finiteMatrixLiftValue_stage f hf,finiteMatrixLiftValue_stage f hf,finiteMatrixLiftValue_stage f hf,map_add]
  map_mul' x y := by
    obtain ⟨n,M,N,rfl,rfl⟩ := finiteMatrix_common_stage x y
    have he : finiteMatrixStage n (M*N) = finiteMatrixStage n M * finiteMatrixStage n N := Subtype.ext (map_mul _ _ _)
    rw [← he,finiteMatrixLiftValue_stage f hf,finiteMatrixLiftValue_stage f hf,finiteMatrixLiftValue_stage f hf,map_mul]
  map_smul' c x := by
    obtain ⟨n,M,rfl⟩ := finiteMatrixStage_surjective x
    have he : finiteMatrixStage n (c • M) = c • finiteMatrixStage n M := Subtype.ext (map_smul _ _ _)
    rw [← he,finiteMatrixLiftValue_stage f hf,finiteMatrixLiftValue_stage f hf,map_smul]
    rfl
  map_star' x := by
    obtain ⟨n,M,rfl⟩ := finiteMatrixStage_surjective x
    have he : finiteMatrixStage n (star M) = star (finiteMatrixStage n M) := Subtype.ext (map_star _ _)
    rw [← he,finiteMatrixLiftValue_stage f hf,finiteMatrixLiftValue_stage f hf,map_star]

lemma finiteMatrixLift_norm_le (x : finiteMatrixSubalgebra (A := A)) : ‖finiteMatrixLift f hf x‖ ≤ ‖x‖ := by
  obtain ⟨n,M,rfl⟩ := finiteMatrixStage_surjective x
  change ‖finiteMatrixLiftValue f (finiteMatrixStage n M)‖ ≤ ‖matrixLimitStage n M‖
  rw [finiteMatrixLiftValue_stage f hf,matrixLimitStage_norm]
  exact NonUnitalStarAlgHom.norm_apply_le (f n) M

def matrixLimitLift : MatrixLimit A →⋆ₙₐ[ℂ] B :=
  extendDenseStarHom finiteMatrixSubalgebra (finiteMatrixLift f hf)
    (finiteMatrixLift_norm_le f hf) finiteMatrixSubalgebra_dense

@[simp] theorem matrixLimitLift_stage (n : ℕ) (M : FinMatrix A n) :
    matrixLimitLift f hf (matrixLimitStage n M) = f n M := by
  change extendDenseStarHom _ _ _ _ ((finiteMatrixStage n M : finiteMatrixSubalgebra) : MatrixLimit A) = _
  rw [extendDenseStarHom_eq]
  exact finiteMatrixLiftValue_stage f hf n M
end CuntzTrace

end

end OAI
