import OAI.NumberTheory.DukePrimeDegree.Geometry.WeakStableFactorization

namespace OAI

/-! # Fine recurrent lifts eliminate the neutral diagonal

Bounded future conjugates are upper triangular. If these same conjugates
enter arbitrarily small identity neighborhoods, their unchanged diagonal
entries are one, so the displacement is a genuine upper-root word.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem upperRootWord_of_bounded_fine_conjugates {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (hord : StrictMono ell)
    (g : G n) (B : ℝ)
    (hbound : ∀ k : ℕ, ∀ i j,
      |(diagonalOneParameter ell hell (k:ℝ)*g*
        diagonalOneParameter ell hell (-(k:ℝ))).val i j| ≤ B)
    (hfine : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ,
      diagonalOneParameter ell hell (k:ℝ)*g*
        diagonalOneParameter ell hell (-(k:ℝ)) ∈ matrixBall n ε) :
    ∃ u : UpperRootTime n, (completeRootChain n).word u=g := by
  have hdiag (i : Fin n) : g.val i i=1 := by
    have hab : |g.val i i-1|=0 := by
      apply le_antisymm _ (abs_nonneg _)
      by_contra h
      have hp : 0 < |g.val i i-1| := lt_of_not_ge h
      obtain ⟨k,hk⟩ := hfine _ hp
      have hi := hk i i
      simp only [conjugation_entry,sub_self,zero_mul,Real.exp_zero,one_mul,
        Matrix.one_apply_eq] at hi
      exact (lt_irrefl _ hi)
    exact sub_eq_zero.mp (abs_eq_zero.mp hab)
  have hpattern : PositiveRootPattern (allPositiveRoots n) g := by
    intro i j hij
    have hnlt : ¬ i < j := by simpa [allPositiveRoots] using hij
    by_cases he : i=j
    · subst j
      simpa only [Matrix.one_apply_eq] using hdiag i
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hnlt) (Ne.symm he)
      rw [Matrix.one_apply_ne he]
      exact conjugation_expanding_entry_eq_zero ell hell g
        tendsto_natCast_atTop_atTop B (Eventually.of_forall hbound) (hord hji)
  have hm : g ∈ positiveRootGeneratedGroup (allPositiveRoots n) :=
    positiveRootPattern_mem_generated (allPositiveRoots n)
      (fun p hp => (Finset.mem_filter.mp hp).2) (allPositiveRoots_closed n) hpattern
  exact upperRootWord_surjective n ⟨g,hm⟩

end DukePrimeDegree

end

end OAI
