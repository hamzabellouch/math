import OAI.Combinatorics.ExpectationThreshold.SelectorDefinitions
import OAI.Combinatorics.ExpectationThreshold.SelectorCountingWordsProducts
import OAI.Combinatorics.ExpectationThreshold.TupleGeometric

namespace OAI

/-!
# Summing the full-profile weights

The reconstruction sets may depend on the entire profile. Once their counting
bound has been replaced by the uniform entropy bound, the remaining full
profiles can be grouped by row counts. The literal word-count weights have
total mass at most one within each such group.
-/

open scoped BigOperators

namespace TalagrandThreshold.Selector

/-- The full-profile sum satisfies the selector budget for any finite family
whose row-count vectors are nonzero. No independence of the rows of the
profile family is required. -/
theorem sum_profile_weights_lt_one_twentieth (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (N : Finset (Profile s))
    (hN : ∀ n ∈ N, rowCount n ≠ 0) :
    (∑ n ∈ N,
      (∏ i : Fin s, ((3 : ℝ) / 64 ^ (i.val + 1)) ^ (rowCount n i)) *
      (∏ i : Fin s, ((wordCount (rowCount n i) (n i) : ℝ) *
        ∏ h : Color s, colorProb p s h ^ (n i h)))) < 1 / 20 := by
  classical
  let c : (Fin s → ℕ) → ℝ := fun t =>
    ∏ i : Fin s, ((3 : ℝ) / 64 ^ (i.val + 1)) ^ (t i)
  let w : (Fin s → ℕ) → Profile s → ℝ := fun t n =>
    ∏ i : Fin s, ((wordCount (t i) (n i) : ℝ) *
      ∏ h : Color s, colorProb p s h ^ (n i h))
  let T : Finset (Fin s → ℕ) := N.image rowCount
  have hc (t : Fin s → ℕ) : 0 ≤ c t := by
    exact Finset.prod_nonneg fun i _ =>
      pow_nonneg (div_nonneg (by norm_num) (pow_nonneg (by norm_num) _)) _
  have hfiber (t : Fin s → ℕ) :
      (∑ n ∈ N.filter (fun n => rowCount n = t),
        c (rowCount n) * w (rowCount n) n) ≤ c t := by
    have hw : (∑ n ∈ N.filter (fun n => rowCount n = t), w t n) ≤ 1 :=
      sum_prod_wordCount_weight_le_one t (N.filter (fun n => rowCount n = t))
        (colorProb p s) (colorProb_nonneg p s hp hs) (sum_colorProb p s).le
    calc
      (∑ n ∈ N.filter (fun n => rowCount n = t),
          c (rowCount n) * w (rowCount n) n) =
          c t * ∑ n ∈ N.filter (fun n => rowCount n = t), w t n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [(Finset.mem_filter.mp hn).2]
      _ ≤ c t * 1 := mul_le_mul_of_nonneg_left hw (hc t)
      _ = c t := mul_one _
  have hT : ∀ t ∈ T, t ≠ 0 := by
    intro t ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    exact hN n hn
  change (∑ n ∈ N, c (rowCount n) * w (rowCount n) n) < 1 / 20
  calc
    (∑ n ∈ N, c (rowCount n) * w (rowCount n) n) =
        ∑ t ∈ T, ∑ n ∈ N.filter (fun n => rowCount n = t),
          c (rowCount n) * w (rowCount n) n :=
      (Finset.sum_fiberwise_of_maps_to
        (fun n hn => Finset.mem_image_of_mem rowCount hn)
        (fun n => c (rowCount n) * w (rowCount n) n)).symm
    _ ≤ ∑ t ∈ T, c t := Finset.sum_le_sum fun t _ => hfiber t
    _ < 1 / 20 := tuple_geometric_sum_lt_one_twentieth T hT

end TalagrandThreshold.Selector

end OAI
