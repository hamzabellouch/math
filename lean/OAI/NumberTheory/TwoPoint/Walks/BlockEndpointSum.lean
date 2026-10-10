import OAI.NumberTheory.TwoPoint.Walks.RetainedLiouvilleEdges
import OAI.NumberTheory.TwoPoint.Bounds.OverlapPrefix

namespace OAI

/-! Summing a directed edge over the finite block keeps precisely those
starting positions whose terminal endpoint remains in the block. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma block_endpoint_sum (M r : ℕ) (i : Fin M) (c : ℤ) (F : ℤ → ℂ) :
    (∑ j : Fin M, if (j.val : ℤ) + c = (i.val : ℤ) + c + r then F ((j.val : ℤ) + c) else 0) =
      if i.val + r < M then F ((i.val : ℤ) + c + r) else 0 := by
  by_cases hi : i.val + r < M
  · let j₀ : Fin M := ⟨i.val + r, hi⟩
    have he (j : Fin M) : (j.val : ℤ) + c = (i.val : ℤ) + c + r ↔ j = j₀ := by
      constructor
      · intro hj
        apply Fin.ext
        dsimp only [j₀]
        omega
      · rintro rfl
        dsimp only [j₀]
        push_cast
        ring
    simp only [he, sum_ite_eq', mem_univ, ite_true, hi]
    congr 1
    dsimp [j₀]
    ring
  · have he (j : Fin M) : (j.val : ℤ) + c ≠ (i.val : ℤ) + c + r := by
      intro hj
      have hjM := j.isLt
      omega
    simp [he, hi]

lemma block_supported_edge_sum (M r : ℕ) (c : ℤ) (F : ℤ → ℤ → ℂ)
    (hsupport : ∀ n m : ℤ, m ≠ n + r → F n m = 0) (i : Fin M) :
    (∑ j : Fin M, F ((i.val : ℤ) + c) ((j.val : ℤ) + c)) =
      if i.val + r < M then F ((i.val : ℤ) + c) ((i.val : ℤ) + c + r) else 0 := by
  have he (j : Fin M) : F ((i.val : ℤ) + c) ((j.val : ℤ) + c) =
      if (j.val : ℤ) + c = (i.val : ℤ) + c + r then
        F ((i.val : ℤ) + c) ((j.val : ℤ) + c) else 0 := by
    split_ifs with h
    · rfl
    · exact hsupport _ _ h
  calc
    _ = ∑ j : Fin M, if (j.val : ℤ) + c = (i.val : ℤ) + c + r then
        F ((i.val : ℤ) + c) ((j.val : ℤ) + c) else 0 := sum_congr rfl (fun j _ => he j)
    _ = _ := block_endpoint_sum M r i c (F ((i.val : ℤ) + c))

lemma retainedLiouvilleEdge_support (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop)
    (h d q : ℕ) (n m : ℤ) (hm : m ≠ n + (h * q * d : ℕ)) :
    retainedLiouvilleEdge Q u eligible g center L K extra keep h d q n m = 0 := by
  unfold retainedLiouvilleEdge
  split_ifs with he
  · exact (hm he.2.2.2.1).elim
  · rfl

lemma retainedLiouvilleEdge_block_sum (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop)
    (h d q M : ℕ) (c : ℤ) (i : Fin M) :
    (∑ j : Fin M, retainedLiouvilleEdge Q u eligible g center L K extra keep h d q
      ((i.val : ℤ) + c) ((j.val : ℤ) + c)) =
      if i.val + h * q * d < M then
        retainedLiouvilleEdge Q u eligible g center L K extra keep h d q
          ((i.val : ℤ) + c) ((i.val : ℤ) + c + (h * q * d : ℕ)) else 0 :=
  block_supported_edge_sum M (h * q * d) c _
    (retainedLiouvilleEdge_support Q u eligible g center L K extra keep h d q) i

end TwoPointCorrelations

end OAI
