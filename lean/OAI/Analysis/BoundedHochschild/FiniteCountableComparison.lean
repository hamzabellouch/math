import OAI.Analysis.BoundedHochschild.ProjectionJoinComparison
import OAI.Analysis.BoundedHochschild.ProjectionSequenceLimits

namespace OAI

/-! Countable joins bounded by a finite orthogonal target. -/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Countably many projections, each embeddable into mutually orthogonal
subprojections of a finite projection, have a join embeddable there. -/
theorem countable_join_subequivalence (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {Q : M} (hQ : IsStarProjection Q) (hfinite : FiniteCorner Q)
    (p q : ℕ → M) (hp : ∀ n, IsStarProjection (p n))
    (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (hqQ : ∀ n, q n ≤ Q)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q n) :
    ∃ v : PartialIso M, v.final ≤ Q ∧ (∀ n, p n ≤ v.initial) ∧
      ∀ r : M, IsStarProjection r → (∀ n, p n ≤ r) → v.initial ≤ r := by
  classical
  choose a haf hau hal using finite_join_subequivalence e p q hp hq horth hembed
  have hsumQ (n : ℕ) : (∑ i ∈ Finset.range n, q i) ≤ Q := by
    apply ((orthogonal_projection_sum_range q hq horth n).le_iff_mul_eq_right hQ).mpr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact ((hq i).le_iff_mul_eq_right hQ).mp (hqQ i)
  have ham : Monotone (fun n => (a n).initial) := monotone_nat_of_le_succ fun n => by
    apply hal n (a (n + 1)).initial (a (n + 1)).initial_proj
    intro i hi
    exact hau (n + 1) i (Nat.lt_succ_of_lt hi)
  have haQ (n : ℕ) : (a n).final ≤ Q := (haf n).trans (hsumQ n)
  obtain ⟨v, hvQ, hvupper, hvleast⟩ := finite_increasing_subequivalence e hQ hfinite
    (fun n => (a n).initial) ham (fun n => ⟨a n, rfl, haQ n⟩)
  refine ⟨v, hvQ, ?_, ?_⟩
  · intro n
    exact (hau (n + 1) n (Nat.lt_succ_self n)).trans (hvupper (n + 1))
  · intro r hr hpr
    apply hvleast r hr
    intro n
    exact hal n r hr (fun i _ => hpr i)

end KadisonRingrose
end BoundedHochschild

end

end OAI
