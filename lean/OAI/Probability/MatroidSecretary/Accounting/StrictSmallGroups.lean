import OAI.Probability.MatroidProphet.Main

namespace OAI

namespace MatroidProphet
open Finset

lemma sum_zpow_lt_two (B : ℝ) (hB : 2 ≤ B) (s : Finset ℤ) (l : ℤ)
    (hsl : ∀ i ∈ s, i ≤ l) :
    (∑ i ∈ s, B ^ i) < 2 * B ^ l := by
  have hB1 : 1 < B := lt_of_lt_of_le (by norm_num) hB
  have hs := sum_zpow_lt_upper B hB1 s (l + 1)
    (fun i hi => by have := hsl i hi; omega)
  have hp : 0 < B ^ l := zpow_pos (by linarith) _
  have hden : 0 < B - 1 := by linarith
  have hratio : B / (B - 1) ≤ 2 := (div_le_iff₀ hden).mpr (by linarith)
  rw [zpow_add_one₀ (ne_of_gt (zero_lt_one.trans hB1)), mul_div_assoc] at hs
  nlinarith

lemma sum_zpow_lt_two_of_pos_bound (B : ℝ) (hB : 2 ≤ B) (levels : Finset ℤ)
    (m : ℝ) (hm : 0 < m) (hbound : ∀ i ∈ levels, B ^ i ≤ m) :
    (∑ i ∈ levels, B ^ i) < 2 * m := by
  classical
  by_cases hn : levels.Nonempty
  · have h := sum_zpow_lt_two B hB levels (levels.max' hn)
      (fun i hi => levels.le_max' i hi)
    exact h.trans_le (mul_le_mul_of_nonneg_left
      (hbound _ (levels.max'_mem hn)) (by norm_num))
  · have he : levels = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty]
    positivity

lemma small_group_mass_strict (B κ m : ℝ) (hB : 2 ≤ B) (hκ : 0 < κ) (hm : 0 < m)
    (levels : Finset ℤ) (Y : ℤ → ℝ) (hY : ∀ i ∈ levels, Y i ≤ κ)
    (hbound : ∀ i ∈ levels, B ^ i ≤ m) :
    (∑ i ∈ levels, B ^ i * Y i) < 2 * κ * m := by
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  calc
    _ ≤ ∑ i ∈ levels, B ^ i * κ :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hY i hi) (zpow_pos hB0 i).le
    _ = κ * ∑ i ∈ levels, B ^ i := by rw [← Finset.sum_mul]; ring
    _ < κ * (2 * m) := mul_lt_mul_of_pos_left
      (sum_zpow_lt_two_of_pos_bound B hB levels m hm hbound) hκ
    _ = _ := by ring

lemma maximumRounded_pos_of_optimum_pos {n : ℕ} (M : Matroid (Fin n)) (w : Weights n)
    (hW : 0 < optimum M (fun e => roundedWeight weightBase (w e))) :
    0 < maximumRounded M w := by
  classical
  by_contra! hm
  have hopt : optimum M (fun e => roundedWeight weightBase (w e)) ≤ 0 := by
    apply optimum_le_of_independent_bound M _ 0 le_rfl
    intro I hI
    apply Finset.sum_nonpos
    intro e he
    have hei : M.Indep ({e} : Set (Fin n)) := hI.subset (by
      intro f hf
      have hfe : f = e := Set.mem_singleton_iff.mp hf
      change f ∈ I
      rwa [hfe])
    exact (roundedWeight_le_maximumRounded M w e hei).trans hm
  exact (not_lt_of_ge hopt) hW

namespace MainAlgorithm

/-- Exact strict version of the discarded-group bound in the positive-W case. -/
lemma small_comparison_mass_strict {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (w : Weights n) (H : Finset (Fin n))
    (hW : 0 < optimum M (fun e => roundedWeight weightBase (w e))) :
    comparisonMass M (fun e => roundedLevel weightBase (w e)) H <
      analyzedComparisonMass M (fun e => roundedLevel weightBase (w e)) H +
        2 * densityThreshold * maximumRounded M w := by
  classical
  let a : Fin n → Option ℤ := fun e => roundedLevel weightBase (w e)
  let Y := positiveGreedy M a \ H
  let U := candidateLabels M a H
  let L := trueLevels M a H
  let A := analyzedLevels M a H
  have hAU : A ⊆ L := Finset.filter_subset _ _
  have hsmall : ∀ i ∈ L \ A, ((Y.filter (fun e => a e = some i)).card : ℝ) ≤ densityThreshold := by
    intro i hi
    obtain ⟨hiL, hiA⟩ := Finset.mem_sdiff.mp hi
    have hn : ¬densityThreshold ≤ ((U.filter (fun e => a e = some i)).card : ℝ) := by
      intro hh
      exact hiA (Finset.mem_filter.mpr ⟨hiL, hh⟩)
    have hc : (Y.filter (fun e => a e = some i)).card ≤ (U.filter (fun e => a e = some i)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (positiveGreedy_survivors_subset M a H))
    have hcR : ((Y.filter (fun e => a e = some i)).card : ℝ) ≤
        ((U.filter (fun e => a e = some i)).card : ℝ) := by exact_mod_cast hc
    exact hcR.trans (le_of_lt (lt_of_not_ge hn))
  have hbound := small_group_mass_strict weightBase densityThreshold (maximumRounded M w)
    (by norm_num [weightBase]) constants_positive.2.1 (maximumRounded_pos_of_optimum_pos M w hW)
    (L \ A) (fun i => ((Y.filter (fun e => a e = some i)).card : ℝ)) hsmall
    (fun i hi => candidate_level_le_maximumRounded M hE w H i (Finset.mem_sdiff.mp hi).1)
  have hpartition := Finset.sum_sdiff hAU
    (f := fun i => weightBase ^ i * ((Y.filter (fun e => a e = some i)).card : ℝ))
  rw [comparisonMass_partition]
  change (∑ i ∈ L, weightBase ^ i * ((Y.filter (fun e => a e = some i)).card : ℝ)) <
    (∑ i ∈ A, weightBase ^ i * ((Y.filter (fun e => a e = some i)).card : ℝ)) + _
  linarith

end MainAlgorithm
end MatroidProphet

end OAI
