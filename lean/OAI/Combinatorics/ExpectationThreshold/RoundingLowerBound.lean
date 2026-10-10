import OAI.Combinatorics.ExpectationThreshold.RoundingMasses
import OAI.Combinatorics.ExpectationThreshold.RoundingColorProducts
import OAI.Combinatorics.ExpectationThreshold.RoundingExpectation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# The deterministic lower bound for rounding

A weighted average at most two places at least half the mass on subsets with
average at most four. On those subsets the quotient-of-powers product is at
least one, yielding the lower bound one quarter for the full product score.
This statement is pointwise in the coloring and needs no independence premise.
-/

open scoped BigOperators

namespace TalagrandThreshold

/-- Finite weighted Markov inequality in the form used by rounding. -/
theorem half_mass_of_weighted_average_le {β : Type*} (T : Finset β)
    (w v : β → ℝ) (hw : ∀ i ∈ T, 0 ≤ w i) (hv : ∀ i ∈ T, 0 ≤ v i)
    (hmean : (∑ i ∈ T, w i * v i) ≤ 2 * (∑ i ∈ T, w i)) :
    (∑ i ∈ T, w i) / 2 ≤ ∑ i ∈ T.filter (fun i => v i ≤ 4), w i := by
  classical
  have hpoint (i : β) (hi : i ∈ T) :
      4 * w i ≤ w i * v i + 4 * (if v i ≤ 4 then w i else 0) := by
    by_cases hgood : v i ≤ 4
    · simp only [ite_eq_left hgood]
      have hnonneg := mul_nonneg (hw i hi) (hv i hi)
      linarith
    · simp only [ite_eq_right hgood, mul_zero, add_zero]
      calc
        4 * w i = w i * 4 := mul_comm _ _
        _ ≤ w i * v i :=
          mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hgood)) (hw i hi)
  have hsum : 4 * (∑ i ∈ T, w i) ≤
      (∑ i ∈ T, w i * v i) + 4 * (∑ i ∈ T.filter (fun i => v i ≤ 4), w i) := by
    calc
      _ = ∑ i ∈ T, 4 * w i := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ T, (w i * v i + 4 * (if v i ≤ 4 then w i else 0)) :=
        Finset.sum_le_sum hpoint
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_filter,
          mul_ite, mul_zero]
  linarith

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem subsetAverage_nat_nonneg (a : α → ℕ) (S : Finset α) :
    0 ≤ subsetAverage (fun x => (a x : ℝ)) S := by
  unfold subsetAverage
  exact div_nonneg (Finset.sum_nonneg (fun x _ => Nat.cast_nonneg (a x)))
    (Nat.cast_nonneg S.card)

omit [Fintype α] [DecidableEq α] in
theorem sum_le_four_card_of_subsetAverage_le (a : α → ℕ) {S : Finset α}
    (hS : S.Nonempty) (haverage : subsetAverage (fun x => (a x : ℝ)) S ≤ 4) :
    (∑ x ∈ S, a x) ≤ 4 * S.card := by
  have hcard : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
  have hreal : (∑ x ∈ S, (a x : ℝ)) ≤ 4 * (S.card : ℝ) :=
    (div_le_iff₀ hcard).mp haverage
  exact_mod_cast hreal

/-- The fractional member mass and its mean color force a product-score lower
bound. Natural colors can include zero; the actual selector uses `val + 1`. -/
theorem productScore_lower_of_mean (g : Finset α → ℝ) (H : Finset α)
    (a : α → ℕ) (hg : ∀ S, 0 ≤ g S) (hMH : (1 / 2 : ℝ) ≤ memberMass g H)
    (hmean : (∑ x : α, (a x : ℝ) * roundingMass g H x) ≤ 2) :
    (1 / 4 : ℝ) ≤ productScore g (fun x => (512 : ℝ) ^ 4 / (512 : ℝ) ^ a x) := by
  classical
  have hMpos : 0 < memberMass g H := by linarith
  have hweighted :
      (∑ S ∈ nonemptySubsets H, g S * subsetAverage (fun x => (a x : ℝ)) S) ≤
        2 * memberMass g H := by
    apply (div_le_iff₀ hMpos).mp
    rw [← roundingMass_mean g H (fun x => (a x : ℝ))]
    exact hmean
  let G := (nonemptySubsets H).filter
    (fun S => subsetAverage (fun x => (a x : ℝ)) S ≤ 4)
  have hgood : memberMass g H / 2 ≤ ∑ S ∈ G, g S := by
    simpa only [G, memberMass] using
      half_mass_of_weighted_average_le (nonemptySubsets H) g
        (fun S => subsetAverage (fun x => (a x : ℝ)) S)
        (fun S _ => hg S) (fun S _ => subsetAverage_nat_nonneg a S) hweighted
  have hsub : G ⊆ (Finset.univ.erase ∅ : Finset (Finset α)) := by
    intro S hS
    have hS' : S ∈ nonemptySubsets H := (Finset.mem_filter.mp hS).1
    have hSne : S ≠ ∅ := (mem_nonemptySubsets.mp hS').1
    exact Finset.mem_erase.mpr ⟨hSne, Finset.mem_univ S⟩
  have hproduct (S : Finset α) (hS : S ∈ G) :
      1 ≤ ∏ x ∈ S, (512 : ℝ) ^ 4 / (512 : ℝ) ^ a x := by
    have hS' := Finset.mem_filter.mp hS
    have hSne : S ≠ ∅ := (mem_nonemptySubsets.mp hS'.1).1
    exact one_le_colorProduct_of_sum_le S a
      (sum_le_four_card_of_subsetAverage_le a
        (Finset.nonempty_iff_ne_empty.mpr hSne) hS'.2)
  have hY (x : α) : 0 ≤ (512 : ℝ) ^ 4 / (512 : ℝ) ^ a x :=
    div_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
  calc
    (1 / 4 : ℝ) ≤ memberMass g H / 2 := by linarith
    _ ≤ ∑ S ∈ G, g S := hgood
    _ ≤ ∑ S ∈ G, g S * ∏ x ∈ S, (512 : ℝ) ^ 4 / (512 : ℝ) ^ a x := by
      apply Finset.sum_le_sum
      intro S hS
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hproduct S hS) (hg S)
    _ ≤ productScore g (fun x => (512 : ℝ) ^ 4 / (512 : ℝ) ^ a x) := by
      unfold productScore
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun S _ _ => mul_nonneg (hg S) (Finset.prod_nonneg (fun x _ => hY x)))

end TalagrandThreshold

end OAI
