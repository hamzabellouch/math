import OAI.Combinatorics.BalancedRyser.Incidence.AffineSecondMoment
import OAI.Combinatorics.BalancedRyser.Incidence.ElementaryIncidence

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace AtypicalLines

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem card_large_abs_le (a : ι → ℝ) (r B : ℝ) (hr : 0 < r)
    (hsum : ∑ i, a i ^ 2 ≤ B) :
    ((Finset.univ.filter (fun i => r < |a i|)).card : ℝ) ≤ B / r ^ 2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos hr)).2
  calc
    ((Finset.univ.filter (fun i => r < |a i|)).card : ℝ) * r ^ 2 =
        ∑ i ∈ Finset.univ.filter (fun i => r < |a i|), r ^ 2 := by simp
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => r < |a i|), a i ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply le_of_lt
      apply sq_lt_sq.mpr
      simpa [abs_of_pos hr] using (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i, a i ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i hi hnot
      exact sq_nonneg _
    _ ≤ B := hsum

theorem normalized_sum_sq_le (a : ι → ℝ) (q N : ℝ) (hq : 0 < q)
    (hsum : ∑ i, (a i - N / q) ^ 2 ≤ q ^ 3 / 4) :
    ∑ i, (a i / q - N / q ^ 2) ^ 2 ≤ q / 4 := by
  have heq (i : ι) : (a i / q - N / q ^ 2) ^ 2 =
      (a i - N / q) ^ 2 / q ^ 2 := by
    field_simp
  simp_rw [heq]
  rw [← Finset.sum_div]
  apply (div_le_iff₀ (sq_pos_of_pos hq)).2
  nlinarith [hsum]

theorem card_normalized_deviation_le (a : ι → ℝ) (q N ε : ℝ)
    (hq : 0 < q) (hε : 0 < ε)
    (hsum : ∑ i, (a i - N / q) ^ 2 ≤ q ^ 3 / 4) :
    ((Finset.univ.filter (fun i => ε < |a i / q - N / q ^ 2|)).card : ℝ) ≤
      q / (4 * ε ^ 2) := by
  have h := card_large_abs_le (fun i => a i / q - N / q ^ 2) ε (q / 4) hε
    (normalized_sum_sq_le a q N hq hsum)
  convert h using 1
  ring

theorem weighted_mark_mass_le (a p : ι → ℝ) (q N ε C : ℝ)
    (hq : 0 < q) (hε : 0 < ε) (hC : 0 ≤ C)
    (hsum : ∑ i, (a i - N / q) ^ 2 ≤ q ^ 3 / 4)
    (hp : ∀ i, p i ≤ C / q ^ 2) :
    (∑ i ∈ Finset.univ.filter (fun i => ε < |a i / q - N / q ^ 2|), p i) ≤
      C / (4 * ε ^ 2 * q) := by
  classical
  have hc := card_normalized_deviation_le a q N ε hq hε hsum
  calc
    (∑ i ∈ Finset.univ.filter (fun i => ε < |a i / q - N / q ^ 2|), p i) ≤
        ∑ i ∈ Finset.univ.filter (fun i => ε < |a i / q - N / q ^ 2|),
          C / q ^ 2 := Finset.sum_le_sum (fun i _ => hp i)
    _ = ((Finset.univ.filter (fun i => ε < |a i / q - N / q ^ 2|)).card : ℝ) *
        (C / q ^ 2) := by simp
    _ ≤ (q / (4 * ε ^ 2)) * (C / q ^ 2) :=
      mul_le_mul_of_nonneg_right hc (div_nonneg hC (sq_nonneg q))
    _ = C / (4 * ε ^ 2 * q) := by
      field_simp

theorem affine_card_marked_lines_le {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (U : Finset (Point F)) (ε : ℝ) (hε : 0 < ε) :
    ((Finset.univ.filter (fun l : Line F =>
      ε < |(affineIntersectionCount U l : ℝ) / (Fintype.card F : ℝ) -
        (U.card : ℝ) / (Fintype.card F : ℝ) ^ 2|)).card : ℝ) ≤
      (Fintype.card F : ℝ) / (4 * ε ^ 2) := by
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := F)
  exact card_normalized_deviation_le
    (fun l : Line F => (affineIntersectionCount U l : ℝ))
    (Fintype.card F : ℝ) (U.card : ℝ) ε hq hε
    (affineSecondMoment_proof (F := F) U).2.2.2.1

end AtypicalLines
end Balanced

end OAI
