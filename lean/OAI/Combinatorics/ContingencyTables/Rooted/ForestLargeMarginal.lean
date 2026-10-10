import OAI.Combinatorics.ContingencyTables.Rooted.ForestPenaltyApplication
import OAI.Combinatorics.ContingencyTables.Rooted.LargePairEnumeration
import OAI.Combinatorics.ContingencyTables.Transport.EqualityReindex

namespace OAI

/-!
# The actual companion large-cell sum has its removal signature

Small coordinates are the actual two views of small cells, and every
large cell is summed once at its physical balance width. All line and
unary factors have the manuscript's row/column and forest parameters.
-/

namespace ContingencyTables.ForestLargeMarginal

open scoped BigOperators Classical
open SimpleGraph
open ForestPenaltyApplication LargePairEnumeration RowColumnPenalties BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def largeMarginal (small : I×J → Bool)
    (T : SimpleGraph (I⊕J)) (b : I → J → ℕ) (ell : I → J → ℤ)
    (M : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (alpha : ℝ)
    {n : ℕ} (e : Fin n ≃ LargeCell small) (z : SmallView small → ℕ) : ℝ :=
  ∑ a : ((k : Fin n) → Fin (M (e k).val.1 (e k).val.2+1)),
    physicalWeight T b ell M r c alpha
      (joinedProfile (fun k => M (e k).val.1 (e k).val.2) z a ∘
        (physicalJoinEquiv small e).symm)

theorem largeMarginal_nonnegative (small : I×J → Bool)
    (T : SimpleGraph (I⊕J)) (b : I → J → ℕ) (ell : I → J → ℤ)
    (M : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (alpha : ℝ)
    {n : ℕ} (e : Fin n ≃ LargeCell small) (z : SmallView small → ℕ) :
    0≤largeMarginal small T b ell M r c alpha e z := by
  apply Finset.sum_nonneg
  intro a _
  exact physicalWeight_nonnegative T b ell M r c alpha _

private theorem largeMarginal_eq_eliminate (small : I×J → Bool)
    (T : SimpleGraph (I⊕J)) (b : I → J → ℕ) (ell : I → J → ℤ)
    (M : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (alpha : ℝ)
    {n : ℕ} (e : Fin n ≃ LargeCell small) :
    largeMarginal small T b ell M r c alpha e=
      BalancedFamily.eliminate (widths (fun k => M (e k).val.1 (e k).val.2)) (fun q =>
        physicalWeight T b ell M r c alpha
          (q ∘ (physicalCoordinateEquiv small e (fun k => M (e k).val.1 (e k).val.2)).symm)) := by
  funext z
  exact (eliminate_eq_actual_cells small e _ (physicalWeight T b ell M r c alpha) z).symm

/-- This is a proved signature of the literal all-large finite count,
with the physical widths, retained small views, and coordinate map made
explicit. -/
theorem largeMarginal_removal (small : I×J → Bool)
    (T : SimpleGraph (I⊕J)) (b : I → J → ℕ) (ell : I → J → ℤ)
    (M : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (alpha : ℝ)
    {n : ℕ} (e : Fin n ≃ LargeCell small) (m : SmallView small → ℕ) (p : ℕ)
    (ha : 0≤alpha) (hwidth : ∀ k, 2≤M (e k).val.1 (e k).val.2) :
    RemovalSlice (largeMarginal small T b ell M r c alpha e) m p := by
  let N : Fin n → ℕ := fun k => M (e k).val.1 (e k).val.2
  have hw : ∀ w ∈ widths N, 2≤w := widths_lower N hwidth
  have hu : ∀ a, 0≤unaryRate T b alpha a := by
    intro a
    unfold unaryRate
    split_ifs
    · exact div_nonneg ha (Nat.cast_nonneg _)
    · exact le_refl 0
  have hs := EqualityReindex.physical_marginal_removal (widths N) m p
    (physicalCoordinateEquiv small e N) cellLine (rootFlag T) (fun _ => alpha)
    (lineOffset ell M r c) viewSlope (unaryRate T b alpha) (unaryEll ell) unarySlope (unaryCap b)
    hw (fun _ => ha) hu
  rw [largeMarginal_eq_eliminate small T b ell M r c alpha e]

  exact hs

/-- Reflecting the retained views and every eliminated large pair proves
the complementary factorial lift's actual addition input. -/
theorem largeMarginal_reflected (small : I×J → Bool)
    (T : SimpleGraph (I⊕J)) (b : I → J → ℕ) (ell : I → J → ℤ)
    (M : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (alpha : ℝ)
    {n : ℕ} (e : Fin n ≃ LargeCell small) (m : SmallView small → ℕ) (p : ℕ)
    (ha : 0≤alpha) (hwidth : ∀ k, 2≤M (e k).val.1 (e k).val.2) :
    RemovalSlice (fun z => largeMarginal small T b ell M r c alpha e
      (IntegerReflection.reflect m z)) m p := by
  let N : Fin n → ℕ := fun k => M (e k).val.1 (e k).val.2
  have hu : ∀ a, 0≤unaryRate T b alpha a := by
    intro a
    unfold unaryRate
    split_ifs
    · exact div_nonneg ha (Nat.cast_nonneg _)
    · exact le_refl 0
  rw [largeMarginal_eq_eliminate small T b ell M r c alpha e]
  exact EqualityReindex.physical_marginal_reflected (widths N) m p
    (physicalCoordinateEquiv small e N) cellLine (rootFlag T) (fun _ => alpha)
    (lineOffset ell M r c) viewSlope (unaryRate T b alpha) (unaryEll ell) unarySlope (unaryCap b)
    (widths_lower N hwidth) (fun _ => ha) hu

end ContingencyTables.ForestLargeMarginal

end OAI
