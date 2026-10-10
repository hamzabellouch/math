import OAI.Analysis.BoundedHochschild.FiniteCountableComparison

namespace OAI

/-! Weak-star null tails of a sequence of orthogonal projections. -/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The tails of an orthogonal projection sum are projections converging
weak-star to zero, and each tail dominates all of its summands. -/
theorem exists_orthogonal_projection_tails (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (q : ℕ → M) (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) :
    ∃ T : ℕ → M, (∀ n, IsStarProjection (T n)) ∧ Antitone T ∧
      (∀ n i, n ≤ i → q i ≤ T n) ∧ PredualTendsto e T atTop 0 := by
  let s (n : ℕ) : M := ∑ i ∈ Finset.range n, q i
  have hs (n : ℕ) : IsStarProjection (s n) := orthogonal_projection_sum_range q hq horth n
  have hsm : Monotone s := monotone_nat_of_le_succ fun n => by
    dsimp [s]
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hq n).nonneg
  obtain ⟨Q, hQ, hlub, ht⟩ := exists_increasing_projection_limit e s hs hsm
  have hsQ (n : ℕ) : s n ≤ Q := hlub.1 ⟨n, rfl⟩
  have hqQ (i : ℕ) : q i ≤ Q := by
    apply le_trans _ (hsQ (i + 1))
    dsimp [s]
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => (hq j).nonneg)
  refine ⟨fun n => Q - s n, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ((hs n).le_iff_sub hQ).mp (hsQ n)
  · intro i j hij
    exact sub_le_sub_left (hsm hij) Q
  · intro n i hni
    have hTail : IsStarProjection (Q - s n) := ((hs n).le_iff_sub hQ).mp (hsQ n)
    apply ((hq i).le_iff_mul_eq_right hTail).mpr
    rw [sub_mul, ((hq i).le_iff_mul_eq_right hQ).mp (hqQ i)]
    have hzero : s n * q i = 0 := by
      dsimp [s]
      rw [Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro j hj
      exact horth j i (Nat.ne_of_lt ((Finset.mem_range.mp hj).trans_le hni))
    rw [hzero, sub_zero]
  · simpa only [sub_self] using
      predual_tendsto_sub e (predual_tendsto_const e Q atTop) ht

end KadisonRingrose
end BoundedHochschild

end

end OAI
