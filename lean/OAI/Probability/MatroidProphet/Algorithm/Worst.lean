import OAI.Probability.MatroidProphet.Algorithm.Statistics
import OAI.Probability.MatroidProphet.Algorithm.Mean
import OAI.Probability.MatroidProphet.WeightedAccounting

namespace OAI

namespace MatroidProphet
open Finset

lemma cumulative_option_weight_bound {α : Type*} [DecidableEq α]
    (B : ℝ) (hB : 2 ≤ B) (A : Finset α) (level : α → Option ℤ) (analyzed : Finset ℤ) :
    (∑ i ∈ analyzed, B ^ i * ((A.filter (fun e => ∃ j, level e = some j ∧ i ≤ j)).card : ℝ)) ≤
      2 * ∑ e ∈ A, levelWeight B (level e) := by
  classical
  let P := A.filter (fun e => level e ≠ none)
  have hfilter (i : ℤ) : P.filter (fun e => i ≤ (level e).getD 0) =
      A.filter (fun e => ∃ j, level e = some j ∧ i ≤ j) := by
    ext e
    cases he : level e <;> simp [P, he]
  have hsum : (∑ e ∈ P, B ^ (level e).getD 0) = ∑ e ∈ A, levelWeight B (level e) := by
    unfold P
    rw [sum_filter]
    apply sum_congr rfl
    intro e he
    cases level e <;> simp [levelWeight]
  have hc := cumulative_weight_bound B hB P (fun e => (level e).getD 0) analyzed
  simpa only [hfilter, hsum] using hc

namespace MainAlgorithm
variable {n : ℕ}

noncomputable def mainWorstRounded (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) : ℝ := by
  classical
  exact univ.inf' univ_nonempty (fun π : ArrivalOrder n =>
    ∑ e ∈ selection M hE d w π, levelWeight weightBase (w e))

lemma mainWorstRounded_le (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n) :
    mainWorstRounded M hE d w ≤ ∑ e ∈ selection M hE d w π, levelWeight weightBase (w e) := by
  classical
  exact inf'_le _ (mem_univ π)

lemma mainWorstRounded_nonneg (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) : 0 ≤ mainWorstRounded M hE d w := by
  classical
  apply le_inf'
  intro π hπ
  apply sum_nonneg
  intro e he
  cases w e with
  | none => exact le_rfl
  | some i => exact (zpow_pos (by norm_num [weightBase]) i).le

lemma weighted_trueLambda_le_selection (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (analyzed : Finset ℤ) (π : ArrivalOrder n) :
    (1/2 : ℝ) * ∑ i ∈ analyzed, weightBase ^ i * (trueLambda M hE d w i : ℝ) ≤
      ∑ e ∈ selection M hE d w π, levelWeight weightBase (w e) := by
  have hc := cumulative_option_weight_bound weightBase (by norm_num [weightBase])
    (selection M hE d w π) w analyzed
  have hr : (∑ i ∈ analyzed, weightBase ^ i * (trueLambda M hE d w i : ℝ)) ≤
      ∑ i ∈ analyzed, weightBase ^ i *
        (((selection M hE d w π).filter (fun e => ∃ j, w e = some j ∧ i ≤ j)).card : ℝ) := by
    apply sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (zpow_pos (by norm_num [weightBase]) i).le
    exact_mod_cast trueLambda_le_count M hE d w π i
  linarith

lemma weighted_trueLambda_le_mainWorstRounded (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (analyzed : Finset ℤ) :
    (1/2 : ℝ) * ∑ i ∈ analyzed, weightBase ^ i * (trueLambda M hE d w i : ℝ) ≤
      mainWorstRounded M hE d w := by
  classical
  apply le_inf'
  intro π hπ
  exact weighted_trueLambda_le_selection M hE d w analyzed π

lemma mainMean_sum {β : Type*} (d : MainMasks n) (I : Finset β) (f : β → MainMasks n → ℝ) :
    mainMean d (fun d' => ∑ i ∈ I, f i d') = ∑ i ∈ I, mainMean d (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [sum_empty, mainMean_const]
  | @insert a I ha ih => simp only [sum_insert ha, mainMean_add, ih]

lemma weighted_mean_trueLambda_le_mainWorstRounded (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (analyzed : Finset ℤ) :
    (1/2 : ℝ) * ∑ i ∈ analyzed, weightBase ^ i * mainMean d (fun d' => (trueLambda M hE d' w i : ℝ)) ≤
      mainMean d (fun d' => mainWorstRounded M hE d' w) := by
  have hh := mainMean_mono d (fun d' _ => weighted_trueLambda_le_mainWorstRounded M hE d' w analyzed)
  simpa only [mainMean_mul, mainMean_sum] using hh

lemma mainWorstRounded_le_hiddenWorstReward (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (r : Seed (mainSeedBits n)) (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    mainWorstRounded M hE (mainMasks r) (fun e => roundedLevel weightBase (w e)) ≤
      hiddenWorstReward (hidden M hE) w r := by
  classical
  apply le_inf'
  intro π hπ
  exact (mainWorstRounded_le M hE (mainMasks r) _ π).trans
    (rounded_selection_le_hiddenReward M hE r w hw π)

end MainAlgorithm
end MatroidProphet

end OAI
