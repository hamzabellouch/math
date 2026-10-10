import OAI.Analysis.Pureness.Stabilization.MatrixPermutation
import OAI.Analysis.Pureness.Stabilization.MatrixEntries

namespace OAI
noncomputable section
open scoped CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A]

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

variable [PartialOrder A] [StarOrderedRing A]

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
end CuntzTrace

end

end OAI
