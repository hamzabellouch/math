import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.FiniteCuntzStates

namespace OAI


noncomputable section
namespace Pureness
open TraceCone
open scoped CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def finiteSumColumn (n : ℕ) : CStarMatrix (Fin n × Fin 2) (Fin n × Fin 2) A :=
  fun i j => if j.2 = 0 ∧ i.1 = j.1 then 1 else 0

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrixInterleaveRaw_entry' (n : ℕ) (M N : FinMatrix A n)
    (i j : Fin n × Fin 2) : matrixInterleaveRaw n (M,N) i j =
      if i.2 = j.2 then if i.2 = 0 then M i.1 j.1 else N i.1 j.1 else 0 := rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma finiteSumColumn_sandwich (n : ℕ) (M N : FinMatrix A n) :
    star (finiteSumColumn (A := A) n) * matrixInterleaveRaw n (M,N) * finiteSumColumn n =
      matrixInterleaveRaw n (M+N,0) := by
  apply CStarMatrix.ext
  rintro ⟨i,r⟩ ⟨j,s⟩
  fin_cases r <;> fin_cases s <;>
    simp [finiteSumColumn, matrixInterleaveRaw_entry', CStarMatrix.mul_apply, CStarMatrix.star_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, CStarMatrix.add_apply, apply_ite star]

theorem finitePositiveClass_sum_le (n : ℕ) (M N : Positive (FinMatrix A n)) :
    finitePositiveClass n (Positive.add M N) ≤ finitePositiveClass n M + finitePositiveClass n N := by
  let U := Positive.map (matrixInterleave n) (positiveProduct (Positive.add M N) Positive.zero)
  let V := Positive.map (matrixInterleave n) (positiveProduct M N)
  let e := CStarMatrix.reindexₐ ℂ A (finProdFinEquiv : (Fin n × Fin 2) ≃ Fin (n*2))
  have he := congrArg e (finiteSumColumn_sandwich n M.1 N.1)
  simp only [map_mul, map_star] at he
  have h : TraceCone.CuntzBelow U V := by
    intro ε hε
    refine ⟨e (finiteSumColumn n), ?_⟩
    change ‖star (e (finiteSumColumn n)) * e (matrixInterleaveRaw n (M.1,N.1)) * e (finiteSumColumn n) -
      e (matrixInterleaveRaw n (M.1+N.1,0))‖ < ε
    rw [he, sub_self, norm_zero]
    exact hε
  have hc := (finitePositiveClass_le_iff (n*2) U V).mpr
    ((cuntzSubequiv_iff_shared U V).mpr h)
  change finitePositiveClass (n*2) (Positive.map (matrixInterleave n) (positiveProduct (Positive.add M N) Positive.zero)) ≤
    finitePositiveClass (n*2) (Positive.map (matrixInterleave n) (positiveProduct M N)) at hc
  simpa only [finitePositiveClass_add, finitePositiveClass_zero, add_zero] using hc

theorem finitePositiveClass_sum_bound {ι : Type*} (n : ℕ) (s : Finset ι)
    (M : ι → Positive (FinMatrix A n)) (u : finiteCuntzSubmonoid (A := A))
    (h : ∀ i ∈ s, finitePositiveClass n (M i) ≤ u) :
    finitePositiveClass n ⟨∑ i ∈ s, (M i).1, Finset.sum_nonneg fun i _ => (M i).2⟩ ≤ s.card • u := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change finitePositiveClass n Positive.zero ≤ 0
    rw [finitePositiveClass_zero]
  | @insert i s hi ih =>
    have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have he : (⟨∑ j ∈ insert i s, (M j).1, Finset.sum_nonneg fun j _ => (M j).2⟩ : Positive (FinMatrix A n)) =
        Positive.add (M i) ⟨∑ j ∈ s, (M j).1, Finset.sum_nonneg fun j _ => (M j).2⟩ := by
      apply Subtype.ext
      exact Finset.sum_insert hi
    rw [he, Finset.card_insert_of_notMem hi, succ_nsmul]
    exact (finitePositiveClass_sum_le n _ _).trans (by
      simpa only [add_comm] using add_le_add (h i (Finset.mem_insert_self _ _)) hs)

end Pureness
end

end OAI
