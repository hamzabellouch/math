import OAI.Analysis.Pureness.Quasitrace.CentralQuasitraceCompression
import OAI.Analysis.Pureness.Stabilization.MatrixParityClasses

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma ComplexQuasitrace.matrixPermute_positive {n : ℕ}
    (T : ComplexQuasitrace (FinMatrix A n)) (e : Equiv.Perm (Fin n))
    (M : Positive (FinMatrix A n)) : T (matrixPermute e M.1) = T M.1 := by
  obtain ⟨x,hx,hy⟩ := matrixPermute_factorization e M
  simpa only [hx,hy] using (T.polar x).symm

namespace CompatibleFiniteQuasitrace
variable (F : CompatibleFiniteQuasitrace A)

lemma matrixEmbedding_positive {n m : ℕ} (e : Fin n ↪ Fin m)
    (M : Positive (FinMatrix A n)) :
    F.level m (matrixEmbedding e M.1) = F.level n M.1 := by
  change F.level m (matrixPermute (matrixEmbeddingPermutation e)
    (matrixInclusion (matrixEmbedding_size e) M.1)) = _
  exact ((F.level m).matrixPermute_positive (matrixEmbeddingPermutation e)
    (Positive.map (matrixInclusion (matrixEmbedding_size e)) M)).trans (F.inclusion _ M.1)

lemma block_left (n : ℕ) (M : Positive (FinMatrix A n)) :
    F.level (n*2) (matrixInterleave n (M.1,0)) = F.level n M.1 := by
  have h := F.matrixEmbedding_positive (matrixParityEmbedding n 0) M
  simpa only [matrixParity_embedding,ite_true] using h

lemma block_right (n : ℕ) (M : Positive (FinMatrix A n)) :
    F.level (n*2) (matrixInterleave n (0,M.1)) = F.level n M.1 := by
  have h := F.matrixEmbedding_positive (matrixParityEmbedding n 1) M
  simpa only [matrixParity_embedding,show (1 : Fin 2) ≠ 0 from by decide,ite_false] using h

theorem block_add (n : ℕ) (M N : Positive (FinMatrix A n)) :
    F.level (n*2) (matrixInterleave n (M.1,N.1)) = F.level n M.1+F.level n N.1 := by
  let L := matrixInterleave n (M.1,0)
  let R := matrixInterleave n (0,N.1)
  have hL : IsSelfAdjoint L :=
    (show IsSelfAdjoint (M.1,(0 : FinMatrix A n)) from
      Prod.ext M.2.star_eq (star_zero _)).map (matrixInterleave n)
  have hR : IsSelfAdjoint R :=
    (show IsSelfAdjoint ((0 : FinMatrix A n),N.1) from
      Prod.ext (star_zero _) N.2.star_eq).map (matrixInterleave n)
  have hc : Commute L R := by
    change matrixInterleave n (M.1,0)*matrixInterleave n (0,N.1) =
      matrixInterleave n (0,N.1)*matrixInterleave n (M.1,0)
    rw [← map_mul,← map_mul]
    congr 1
    simp
  have he : L+R=matrixInterleave n (M.1,N.1) := by
    change matrixInterleave n (M.1,0)+matrixInterleave n (0,N.1)=_
    rw [← map_add]
    congr 1
    simp
  have h := (F.level (n*2)).map_add_commuting_selfAdjoint ⟨L,hL⟩ ⟨R,hR⟩ hc
  change F.level (n*2) (L+R)=F.level (n*2) L+F.level (n*2) R at h
  rw [he] at h
  exact h.trans (congrArg₂ (·+·) (F.block_left n M) (F.block_right n N))

theorem block_add_re (n : ℕ) (M N : Positive (FinMatrix A n)) :
    (F.level (n*2) (matrixInterleave n (M.1,N.1))).re =
      (F.level n M.1).re+(F.level n N.1).re :=
  congrArg Complex.re (F.block_add n M N)

end CompatibleFiniteQuasitrace
end CuntzPureness

end

end OAI
