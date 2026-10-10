import OAI.NumberTheory.Ostmann.Construction.SelectedCellGap
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTargetTotal

namespace OAI

/-! # The original initial log total for the selected actual cells -/
namespace Ostmann
open scoped BigOperators

theorem selected_compensation_centers_sum_bounds
    {A B : Set ℕ} {N hi : ℕ} {a C L Y : ℝ} {D : Finset ℕ}
    {centers : List ℕ} {targets : List ℝ}
    (h : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets) :
    targets.sum ≤ 4 * (centers.map (fun j : ℕ => (j : ℝ))).sum ∧
      4 * (centers.map (fun j : ℕ => (j : ℝ))).sum ≤
        targets.sum + 4 * centers.length * (64 * tailDefectBudget a C Y + 1) := by
  induction h with
  | nil => simp
  | @cons j w js ws hj hrest ih =>
    have hlo := hj.1
    have hhi := hj.2.1
    simp only [List.sum_cons, List.map_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith only [hlo, hhi, ih.1, ih.2]

theorem selected_initial_total_error
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd Δ₀ BD Bz : ℝ}
    {D : Finset ℕ} {centers : List ℕ} (k : ℕ)
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd
        (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
          ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L)) - 2 * cb) / 6) top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers
      (movingCompensationTargets
        (movingProtectedTarget k Y G cd
          (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
            ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L)))
        (movingCompensationGaps k BD Bz L))) :
    |2 * (G + cb + cd + 3 * top +
        2 * (centers.map (fun j : ℕ => (j : ℝ))).sum) - (Y + Δ₀)| ≤
      (6 + 4 * k) * (64 * tailDefectBudget a C Y + 1) := by
  let J := movingProtectedTarget k Y G cd
    (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
      ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L))
  have htotal := moving_protected_and_compensation_total k BD Bz L Y G cd Δ₀
  change 2 * G + 2 * cd + J +
    (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum = Y + Δ₀ at htotal
  have hlen : centers.length = k := by
    have hh := hcenters.length_eq
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using hh
  have hsum := selected_compensation_centers_sum_bounds hcenters
  rw [hlen] at hsum
  have hlo := htop.1
  have hhi := htop.2.1
  change (J - 2 * cb) / 6 ≤ (top : ℝ) at hlo
  change (top : ℝ) ≤ (J - 2 * cb) / 6 + 64 * tailDefectBudget a C Y + 1 at hhi
  change (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum ≤ _ ∧ _ at hsum
  have hnonneg : 0 ≤ 2 * (G + cb + cd + 3 * top +
      2 * (centers.map (fun j : ℕ => (j : ℝ))).sum) - (Y + Δ₀) := by
    linarith only [hlo, hsum.1, htotal]
  rw [abs_of_nonneg hnonneg]
  nlinarith only [hhi, hsum.2, htotal]

end Ostmann

end OAI
