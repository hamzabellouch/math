import OAI.Analysis.Pureness.Stabilization.MatrixFamilies
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra

namespace OAI
noncomputable section
open scoped ENNReal Topology CStarAlgebra
namespace CuntzTrace
variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixUnion : NonUnitalStarSubalgebra ℂ (FamilyQuotient (FinMatrix A)) where
  carrier := {x | ∃ (n : ℕ) (M : FinMatrix A n), matrixStage n M = x}
  zero_mem' := ⟨0,0,map_zero _⟩
  add_mem' := by
    rintro x y ⟨n,M,rfl⟩ ⟨m,N,rfl⟩
    refine ⟨max n m, matrixInclusion (le_max_left n m) M + matrixInclusion (le_max_right n m) N, ?_⟩
    simp
  mul_mem' := by
    rintro x y ⟨n,M,rfl⟩ ⟨m,N,rfl⟩
    refine ⟨max n m, matrixInclusion (le_max_left n m) M * matrixInclusion (le_max_right n m) N, ?_⟩
    simp
  smul_mem' := by
    rintro c x ⟨n,M,rfl⟩
    exact ⟨n,c • M,map_smul _ c M⟩
  star_mem' := by
    rintro x ⟨n,M,rfl⟩
    exact ⟨n,star M,map_star _ M⟩

def matrixLimitAlgebra : NonUnitalStarSubalgebra ℂ (FamilyQuotient (FinMatrix A)) :=
  (matrixUnion A).topologicalClosure

instance matrixLimitAlgebra_closed : IsClosed (matrixLimitAlgebra A : Set (FamilyQuotient (FinMatrix A))) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

abbrev MatrixLimit := matrixLimitAlgebra A

instance : NonUnitalCStarAlgebra (MatrixLimit A) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (matrixLimitAlgebra A)

variable {A}
def matrixLimitStage (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] MatrixLimit A where
  toFun M := ⟨matrixStage n M, NonUnitalStarSubalgebra.le_topologicalClosure _ ⟨n,M,rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' M N := Subtype.ext (map_add _ M N)
  map_mul' M N := Subtype.ext (map_mul _ M N)
  map_smul' c M := Subtype.ext (map_smul _ c M)
  map_star' M := Subtype.ext (map_star _ M)

@[simp] lemma matrixLimitStage_norm (n : ℕ) (M : FinMatrix A n) : ‖matrixLimitStage n M‖ = ‖M‖ :=
  matrixStage_norm n M

lemma matrixLimitStage_isometry (n : ℕ) : Isometry (matrixLimitStage (A := A) n) :=
  AddMonoidHomClass.isometry_of_norm _ (matrixLimitStage_norm n)

@[simp] lemma matrixLimitStage_compatible {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) :
    matrixLimitStage m (matrixInclusion h M) = matrixLimitStage n M :=
  Subtype.ext (matrixStage_compatible h M)

theorem matrixLimit_finite_approximation (x : MatrixLimit A) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (M : FinMatrix A n), ‖x-matrixLimitStage n M‖ < ε := by
  obtain ⟨y,⟨n,M,rfl⟩,hy⟩ := Metric.mem_closure_iff.mp x.2 ε hε
  refine ⟨n,M,?_⟩
  change ‖(x : FamilyQuotient (FinMatrix A))-matrixStage n M‖ < ε
  simpa only [dist_eq_norm] using hy
end CuntzTrace

end

end OAI
