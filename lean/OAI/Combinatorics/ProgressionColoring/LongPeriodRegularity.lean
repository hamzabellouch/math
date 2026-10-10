import OAI.Combinatorics.ProgressionColoring.LongPeriodBlocks
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

/-!
# Counting regular positions in a long-period block

The finite union bound is expressed on literal subsets of the block indices.
The coordinate bounds are supplied by the actual rational-grid count.
-/

namespace QuantitativeVanDerWaerden

open scoped BigOperators

theorem regular_count_of_coordinate_bounds {D h : ℕ}
    (rotating : Finset (Fin D)) (bad : Fin D → Finset (Fin h)) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hcount : ∀ i ∈ rotating, ((bad i).card : ℝ) ≤ (h : ℝ) * ε)
    (hsmall : (D : ℝ) * ε ≤ 1 / 2) :
    (h : ℝ) / 2 ≤ ((Finset.univ \ rotating.biUnion bad).card : ℝ) := by
  classical
  have hunion : ((rotating.biUnion bad).card : ℝ) ≤
      ∑ i ∈ rotating, ((bad i).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := rotating) (t := bad))
  have hsum : (∑ i ∈ rotating, ((bad i).card : ℝ)) ≤
      (rotating.card : ℝ) * ((h : ℝ) * ε) := by
    calc
      _ ≤ ∑ _i ∈ rotating, (h : ℝ) * ε := Finset.sum_le_sum hcount
      _ = _ := by simp
  have hcard : (rotating.card : ℝ) ≤ D := by
    exact_mod_cast (show rotating.card ≤ D by simpa using rotating.card_le_univ)
  have hnonneg : 0 ≤ (h : ℝ) * ε := mul_nonneg (Nat.cast_nonneg h) hε
  have htotal : ((rotating.biUnion bad).card : ℝ) ≤ (h : ℝ) / 2 := by
    calc
      _ ≤ (rotating.card : ℝ) * ((h : ℝ) * ε) := hunion.trans hsum
      _ ≤ (D : ℝ) * ((h : ℝ) * ε) := mul_le_mul_of_nonneg_right hcard hnonneg
      _ = (h : ℝ) * ((D : ℝ) * ε) := by ring
      _ ≤ (h : ℝ) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg h)
      _ = (h : ℝ) / 2 := by ring
  have hsplit : ((Finset.univ \ rotating.biUnion bad).card : ℝ) +
      ((rotating.biUnion bad).card : ℝ) = h := by
    exact_mod_cast (show (Finset.univ \ rotating.biUnion bad).card +
      (rotating.biUnion bad).card = h by
        simpa using Finset.card_sdiff_add_card_eq_card
          (Finset.subset_univ (rotating.biUnion bad)))
  linarith

/-- The finite complement in the union bound is exactly the regular-position
predicate, with equality at the cut-distance threshold retained as regular. -/
theorem regular_positions_eq_complement {D h : ℕ}
    (rotating : Finset (Fin D)) (Y : Fin h → Fin D → ℝ) (η : ℝ) :
    (Finset.univ.filter fun z => ∀ i ∈ rotating, η ≤ rho (Y z i)) =
      Finset.univ \ rotating.biUnion
        (fun i => Finset.univ.filter fun z => rho (Y z i) < η) := by
  classical
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    Finset.mem_biUnion, not_exists, not_and, not_lt]

theorem regular_fraction_constant {D : ℕ} (hD : 3 ≤ D) :
    (D : ℝ) * (4 * (1 / (1000 * (D : ℝ))) + 1 / (D : ℝ) ^ 2) ≤ 1 / 2 := by
  have hDR : (3 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := by linarith
  have hid : (D : ℝ) * (4 * (1 / (1000 * (D : ℝ))) + 1 / (D : ℝ) ^ 2) =
      4 / 1000 + 1 / (D : ℝ) := by
    field_simp [hDpos.ne']
  rw [hid]
  have hrec : 1 / (D : ℝ) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hDR
  linarith

end QuantitativeVanDerWaerden

end OAI
