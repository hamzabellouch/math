import OAI.NumberTheory.Ostmann.QuadraticSieveDoublePoisson
import OAI.NumberTheory.Ostmann.QuadraticSieveDualReindexTail

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap

theorem tsum_oddSquarefree_cutoff (K : ℕ) (f : ℕ → ℂ) :
    (∑' b : OddSquarefreeIndex, if b.val ≤ K then f b.val else 0) =
      ∑ b ∈ oddSquarefreeUpTo K, f b := by
  classical
  change (∑' b : {b : ℕ | Odd b ∧ Squarefree b}, if b.val ≤ K then f b.val else 0) = _
  rw [tsum_subtype {b : ℕ | Odd b ∧ Squarefree b} (fun b => if b ≤ K then f b else 0)]
  rw [tsum_eq_sum (s := oddSquarefreeUpTo K)]
  · apply Finset.sum_congr rfl
    intro b hb
    obtain ⟨hpos,hK,ho,hs⟩ := mem_oddSquarefreeUpTo.mp hb
    simp [ho,hs,hK]
  · intro b hb
    by_cases h : Odd b ∧ Squarefree b ∧ b ≤ K
    · exact (hb (mem_oddSquarefreeUpTo.mpr
        ⟨Nat.pos_of_ne_zero h.2.1.ne_zero,h.2.2,h.1,h.2.1⟩)).elim
    · simp only [Set.indicator_apply]
      split_ifs <;> aesop

theorem tsum_oddSquarefree_eq_prefix_add_tail (K : ℕ) (f : ℕ → ℂ)
    (hf : Summable (fun b : OddSquarefreeIndex => f b.val)) :
    (∑' b : OddSquarefreeIndex, f b.val) =
      (∑ b ∈ oddSquarefreeUpTo K, f b) +
        ∑' b : OddSquarefreeIndex, if (K : ℝ) < (b.val : ℝ) then f b.val else 0 := by
  have hl : Summable (fun b : OddSquarefreeIndex => if b.val ≤ K then f b.val else 0) :=
    (hf.indicator {b | b.val ≤ K}).congr (fun b => by simp [Set.indicator_apply])
  have hr : Summable (fun b : OddSquarefreeIndex => if (K : ℝ) < (b.val : ℝ) then f b.val else 0) :=
    (hf.indicator {b | (K : ℝ) < (b.val : ℝ)}).congr (fun b => by simp [Set.indicator_apply])
  rw [← tsum_oddSquarefree_cutoff K f, ← hl.tsum_add hr]
  apply tsum_congr
  intro b
  simp only [Nat.cast_lt]
  by_cases h : b.val ≤ K <;> simp [h,not_lt_of_ge,lt_of_not_ge]

theorem dualSquarefree_prefix_tail (W : 𝓢(ℝ, ℂ)) (a : ℤ) (e M : ℝ) (q K : ℕ)
    (ha : a ≠ 0) (he : 0 < e) (hM : 0 < M) (hq : 0 < q) :
    (∑' b : OddSquarefreeIndex, (jacobiSym (a * (b.val : ℤ)) q : ℂ) *
      dualSquareSum W (a : ℝ) e M (b.val : ℝ) q) =
      (∑ b ∈ oddSquarefreeUpTo K, (jacobiSym (a * (b : ℤ)) q : ℂ) *
        dualSquareSum W (a : ℝ) e M (b : ℝ) q) + dualSquarefreeTail W a e M q K :=
by
  let f : ℕ → ℂ := fun b => (jacobiSym (a * (b : ℤ)) q : ℂ) *
    dualSquareSum W (a : ℝ) e M (b : ℝ) q
  have hf : Summable (fun b : OddSquarefreeIndex => f b.val) :=
    summable_dualSquareSum_terms W a e M q ha he hM hq
  have h := tsum_oddSquarefree_eq_prefix_add_tail K f hf
  change (∑' b : OddSquarefreeIndex, f b.val) =
    (∑ b ∈ oddSquarefreeUpTo K, f b) +
      ∑' b : OddSquarefreeIndex, if (K : ℝ) < (b.val : ℝ) then f b.val else 0
  exact h

end Ostmann.QuadraticSieve

end OAI
