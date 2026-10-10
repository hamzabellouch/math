import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.MatrixEntries

namespace OAI


noncomputable section
open scoped CStarAlgebra

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma matrixEmbedding_size {n m : ℕ} (e : Fin n ↪ Fin m) : n ≤ m := by
  simpa using Fintype.card_le_of_injective e e.injective

def matrixEmbeddingPermutation {n m : ℕ} (e : Fin n ↪ Fin m) : Equiv.Perm (Fin m) :=
  Classical.choose (Equiv.Perm.exists_extending_pair
    (Fin.castLE (matrixEmbedding_size e)) e (Fin.castLE_injective _) e.injective)

lemma matrixEmbeddingPermutation_apply {n m : ℕ} (e : Fin n ↪ Fin m) (i : Fin n) :
    matrixEmbeddingPermutation e (Fin.castLE (matrixEmbedding_size e) i) = e i :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair
    (Fin.castLE (matrixEmbedding_size e)) e (Fin.castLE_injective _) e.injective) i

def matrixEmbedding {n m : ℕ} (e : Fin n ↪ Fin m) : FinMatrix A n →⋆ₙₐ[ℂ] FinMatrix A m :=
  (matrixPermute (matrixEmbeddingPermutation e)).comp (matrixInclusion (matrixEmbedding_size e))

@[simp] theorem matrixEmbedding_entry {n m : ℕ} (e : Fin n ↪ Fin m)
    (M : FinMatrix A n) (i j : Fin n) : matrixEmbedding e M (e i) (e j) = M i j := by
  rw [← matrixEmbeddingPermutation_apply e i,← matrixEmbeddingPermutation_apply e j]
  change matrixPermute (matrixEmbeddingPermutation e) (matrixInclusion (matrixEmbedding_size e) M) _ _ = _
  rw [matrixPermute_entry,matrixInclusion_entry_inside]

theorem matrixEmbedding_outside {n m : ℕ} (e : Fin n ↪ Fin m)
    (M : FinMatrix A n) (i j : Fin m) (h : i ∉ Set.range e ∨ j ∉ Set.range e) :
    matrixEmbedding e M i j = 0 := by
  obtain ⟨p,rfl⟩ := (matrixEmbeddingPermutation e).surjective i
  obtain ⟨q,rfl⟩ := (matrixEmbeddingPermutation e).surjective j
  change matrixPermute (matrixEmbeddingPermutation e) (matrixInclusion (matrixEmbedding_size e) M) _ _ = _
  rw [matrixPermute_entry]
  apply matrixInclusion_entry_outside
  have hi (p : Fin m) (hp : matrixEmbeddingPermutation e p ∉ Set.range e) : n ≤ p.val := by
    by_contra hn
    have he : Fin.castLE (matrixEmbedding_size e) ⟨p.val,by omega⟩ = p := rfl
    exact hp ⟨⟨p.val,by omega⟩,by rw [← matrixEmbeddingPermutation_apply,he]⟩
  exact h.elim (fun hp => Or.inl (hi p hp)) (fun hq => Or.inr (hi q hq))

theorem matrixEmbedding_ext {n m : ℕ} (e : Fin n ↪ Fin m) (M : FinMatrix A n)
    (N : FinMatrix A m) (hin : ∀ i j, N (e i) (e j) = M i j)
    (hout : ∀ i j, i ∉ Set.range e ∨ j ∉ Set.range e → N i j = 0) :
    matrixEmbedding e M = N := by
  apply CStarMatrix.ext; intro i j
  by_cases hi : i ∈ Set.range e
  · obtain ⟨p,rfl⟩ := hi
    by_cases hj : j ∈ Set.range e
    · obtain ⟨q,rfl⟩ := hj
      rw [matrixEmbedding_entry,hin]
    · rw [matrixEmbedding_outside e M _ _ (Or.inr hj),hout _ _ (Or.inr hj)]
  · rw [matrixEmbedding_outside e M _ _ (Or.inl hi),hout _ _ (Or.inl hi)]

theorem matrixEmbedding_cuntzClass {n m : ℕ} (e : Fin n ↪ Fin m)
    (a : Positive (FinMatrix A n)) :
    CuntzClass.mk (Positive.map (matrixLimitStage m) (Positive.map (matrixEmbedding e) a)) =
      CuntzClass.mk (Positive.map (matrixLimitStage n) a) := by
  have h := congrArg (CuntzClass.map (matrixLimitStage (A := A) m))
    (matrixPermute_cuntzClass (matrixEmbeddingPermutation e)
      (Positive.map (matrixInclusion (matrixEmbedding_size e)) a))
  change CuntzClass.mk (Positive.map (matrixLimitStage m) (Positive.map (matrixEmbedding e) a)) =
    CuntzClass.mk (Positive.map (matrixLimitStage m)
      (Positive.map (matrixInclusion (matrixEmbedding_size e)) a)) at h
  rw [h]
  congr 1
  apply Subtype.ext
  exact matrixLimitStage_compatible _ _
end TraceCone
end


noncomputable section
open scoped Topology CStarAlgebra

namespace TraceCone
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
end TraceCone
end


noncomputable section
open scoped NNReal ENNReal Topology

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def positiveProduct (a b : Positive A) : Positive (A × A) := ⟨(a.1,b.1),a.2,b.2⟩

omit [StarOrderedRing A] in
theorem positiveProduct_cuntzBelow {a b c d : Positive A} (hac : CuntzBelow a c) (hbd : CuntzBelow b d) :
    CuntzBelow (positiveProduct a b) (positiveProduct c d) := by
  intro ε hε
  obtain ⟨v,hv⟩ := hac ε hε
  obtain ⟨w,hw⟩ := hbd ε hε
  refine ⟨(v,w),?_⟩
  change max ‖star v*c.1*v-a.1‖ ‖star w*d.1*w-b.1‖ < ε
  exact max_lt hv hw

def matrixBlockPositive (a b : Positive (MatrixLimit A)) : Positive (MatrixLimit A) :=
  Positive.map matrixBlockHom (positiveProduct a b)

theorem matrixBlockPositive_cuntzBelow {a b c d : Positive (MatrixLimit A)}
    (hac : CuntzBelow a c) (hbd : CuntzBelow b d) :
    CuntzBelow (matrixBlockPositive a b) (matrixBlockPositive c d) :=
  (positiveProduct_cuntzBelow hac hbd).map matrixBlockHom

namespace CuntzClass

def matrixAdd (x y : CuntzClass (MatrixLimit A)) : CuntzClass (MatrixLimit A) :=
  Quotient.lift₂ (fun a b => mk (matrixBlockPositive a b))
    (fun (a b c d : Positive (MatrixLimit A)) (hac : (cuntzSetoid (MatrixLimit A)) a c)
      (hbd : (cuntzSetoid (MatrixLimit A)) b d) =>
      (mk_eq_mk_iff _ _).mpr ⟨matrixBlockPositive_cuntzBelow hac.1 hbd.1,
        matrixBlockPositive_cuntzBelow hac.2 hbd.2⟩) x y

@[simp] lemma matrixAdd_mk (a b : Positive (MatrixLimit A)) :
    matrixAdd (mk a) (mk b) = mk (matrixBlockPositive a b) := rfl

theorem matrixAdd_mono {x y u v : CuntzClass (MatrixLimit A)} (hxu : x ≤ u) (hyv : y ≤ v) :
    matrixAdd x y ≤ matrixAdd u v := by
  induction x using Quotient.inductionOn with | h a =>
  induction y using Quotient.inductionOn with | h b =>
  induction u using Quotient.inductionOn with | h c =>
  induction v using Quotient.inductionOn with | h d =>
  exact matrixBlockPositive_cuntzBelow hxu hyv
end CuntzClass
end TraceCone
end

end OAI
