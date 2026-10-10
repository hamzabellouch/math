import OAI.Combinatorics.BalancedRyser.Incidence.AffineDoubleCount
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Incidence.AffineMomentAlgebraLemmas
import OAI.Combinatorics.BalancedRyser.Incidence.ElementaryIncidence

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [DecidableEq F] in

theorem affine_point_count_le (U : Finset (Point F)) :
    (U.card : ℝ) ≤ (Fintype.card F : ℝ) ^ 2 := by
  have h := Finset.card_le_univ U
  simp only [Point, Fintype.card_prod] at h
  rw [pow_two]
  exact_mod_cast h

omit [Field F] [DecidableEq F] in

theorem affine_line_count_real :
    (Fintype.card (Line F) : ℝ) =
      (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1) := by
  simp only [Line, Direction, Fintype.card_prod, Fintype.card_option,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem affine_second_moment_of_raw_counts
    (hfirst : ∀ U : Finset (Point F),
      ∑ l : Line F, affineIntersectionCount U l =
        (Fintype.card F + 1) * U.card)
    (hsecond : ∀ U : Finset (Point F),
      ∑ l : Line F, affineIntersectionCount U l ^ 2 =
        U.card ^ 2 + Fintype.card F * U.card) :
    AffineSecondMoment F := by
  intro U
  let q : ℝ := Fintype.card F
  let N : ℝ := U.card
  let a : Line F → ℝ := fun l => affineIntersectionCount U l
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos (α := F)
  have hc : (Fintype.card (Line F) : ℝ) = q * (q + 1) :=
    affine_line_count_real
  have h₁ : ∑ l, a l = (q + 1) * N := by
    dsimp [a, q, N]
    exact_mod_cast hfirst U
  have h₂ : ∑ l, a l ^ 2 = N ^ 2 + q * N := by
    dsimp [a, q, N]
    exact_mod_cast hsecond U
  have h₃ := MomentAlgebra.affine_centered_sum a q N hq.ne' hc h₁ h₂
  have h₄ := MomentAlgebra.affine_centered_sum_le a q N hq hc h₁ h₂
  have h₅ : (∑ d : Direction F, affineDirectionalVariance U d) =
      N - N ^ 2 / q ^ 2 := by
    exact MomentAlgebra.directional_variance_sum a q N hq.ne' h₃
  refine ⟨h₁, h₂, h₃, h₄, h₅, ?_, affine_point_count_le U⟩
  rw [h₅]
  exact MomentAlgebra.directional_variance_le_count q N

theorem affineSecondMoment_proof : AffineSecondMoment F := by
  apply affine_second_moment_of_raw_counts
  · intro U
    exact sum_line_count OnLine U (Fintype.card F + 1)
      (fun p _ => card_lines_through p)
  · intro U
    exact sum_sq_line_count_of_unique OnLine U (Fintype.card F)
      (fun p _ => card_lines_through p)
      (fun p _ r _ hne => existsUnique_line_of_ne p r hne)

end Balanced

end OAI
