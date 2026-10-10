import OAI.Analysis.Pureness.Stabilization.MatrixLimitLift
import OAI.Analysis.Pureness.Stabilization.MatrixInterleaveSystem

namespace OAI
noncomputable section
open scoped Topology CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixPairLeft (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] (FinMatrix A n × FinMatrix A n) where
  toFun M := (M,0)
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  map_star' _ := by ext <;> simp

def matrixPairRight (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] (FinMatrix A n × FinMatrix A n) where
  toFun M := (0,M)
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  map_star' _ := by ext <;> simp

def matrixEvenStage (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] MatrixLimit A :=
  (matrixLimitBlock n).comp (matrixPairLeft n)
def matrixOddStage (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] MatrixLimit A :=
  (matrixLimitBlock n).comp (matrixPairRight n)

lemma matrixEvenStage_compatible {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) :
    matrixEvenStage m (matrixInclusion h M) = matrixEvenStage n M := by
  simpa [matrixEvenStage,matrixPairLeft] using matrixLimitBlock_compatible h (M,0)
lemma matrixOddStage_compatible {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) :
    matrixOddStage m (matrixInclusion h M) = matrixOddStage n M := by
  simpa [matrixOddStage,matrixPairRight] using matrixLimitBlock_compatible h (0,M)

def matrixEven : MatrixLimit A →⋆ₙₐ[ℂ] MatrixLimit A := matrixLimitLift matrixEvenStage matrixEvenStage_compatible
def matrixOdd : MatrixLimit A →⋆ₙₐ[ℂ] MatrixLimit A := matrixLimitLift matrixOddStage matrixOddStage_compatible

@[simp] lemma matrixEven_stage (n : ℕ) (M : FinMatrix A n) :
    matrixEven (matrixLimitStage n M) = matrixLimitBlock n (M,0) := matrixLimitLift_stage _ _ _ _
@[simp] lemma matrixOdd_stage (n : ℕ) (M : FinMatrix A n) :
    matrixOdd (matrixLimitStage n M) = matrixLimitBlock n (0,M) := matrixLimitLift_stage _ _ _ _

theorem matrixEven_mul_matrixOdd (x y : MatrixLimit A) : matrixEven x * matrixOdd y = 0 := by
  have he : Continuous (matrixEven (A := A)) := by
    apply LipschitzWith.continuous (K := 1)
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [dist_eq_norm,← map_sub,NNReal.coe_one,one_mul] using
      NonUnitalStarAlgHom.norm_apply_le (matrixEven (A := A)) (a-b)
  have ho : Continuous (matrixOdd (A := A)) := by
    apply LipschitzWith.continuous (K := 1)
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [dist_eq_norm,← map_sub,NNReal.coe_one,one_mul] using
      NonUnitalStarAlgHom.norm_apply_le (matrixOdd (A := A)) (a-b)
  refine finiteMatrixSubalgebra_dense.induction_on₂ ?_ ?_ x y
  · exact isClosed_eq ((he.comp continuous_fst).mul
      (ho.comp continuous_snd)) continuous_const
  · intro u v
    obtain ⟨n,M,N,hu,hv⟩ := finiteMatrix_common_stage u v
    rw [← hu,← hv]
    change matrixEven (matrixLimitStage n M) * matrixOdd (matrixLimitStage n N) = 0
    rw [matrixEven_stage,matrixOdd_stage,← map_mul]
    have hz : (M,0) * (0,N) = (0 : FinMatrix A n × FinMatrix A n) := by simp
    rw [hz,map_zero]

theorem matrixOdd_mul_matrixEven (x y : MatrixLimit A) : matrixOdd x * matrixEven y = 0 := by
  have h := congrArg star (matrixEven_mul_matrixOdd (star y) (star x))
  simpa only [star_mul,← map_star,star_star,star_zero] using h

def matrixBlockHom : (MatrixLimit A × MatrixLimit A) →⋆ₙₐ[ℂ] MatrixLimit A where
  toFun P := matrixEven P.1 + matrixOdd P.2
  map_zero' := by simp
  map_add' P Q := by simp only [Prod.fst_add,Prod.snd_add,map_add]; abel
  map_mul' P Q := by
    simp only [Prod.fst_mul,Prod.snd_mul,map_mul,mul_add,add_mul,
      matrixEven_mul_matrixOdd,matrixOdd_mul_matrixEven,add_zero,zero_add]
  map_smul' c P := by
    change matrixEven (c • P.1) + matrixOdd (c • P.2) = c • (matrixEven P.1 + matrixOdd P.2)
    rw [map_smul,map_smul,smul_add]
  map_star' P := by simp only [Prod.fst_star,Prod.snd_star,map_star,star_add]
end CuntzTrace

end

end OAI
