import OAI.Analysis.MarkovType.CoefficientSequenceOps
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coefficientBasic_half_gain_iterate {M : ℕ} {K : ℝ}
    (hgain : ∀ y : Fin M → E, CoefficientBasic K y →
      ∃ i, ‖y i‖ ≤ (1 / 2 : ℝ) * ‖∑ j, y j‖) :
    ∀ k (x : Fin (M ^ k) → E), CoefficientBasic K x →
      ∃ i, ‖x i‖ ≤ (1 / 2 : ℝ) ^ k * ‖∑ j, x j‖ := by
  intro k
  induction k with
  | zero =>
      simp only [Nat.pow_zero]
      intro x hx
      refine ⟨0, ?_⟩
      rw [pow_zero, one_mul]
      exact (congrArg norm (Fin.sum_univ_one x)).ge
  | succ k ih =>
      have hstep :
          ∀ x : Fin (M * M ^ k) → E, CoefficientBasic K x →
            ∃ i, ‖x i‖ ≤
              (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k * ‖∑ j, x j‖ := by
        intro x hx
        obtain ⟨b, hb⟩ := hgain (equalBlocks x) hx.equalBlocks
        rw [sum_equalBlocks x] at hb
        obtain ⟨i, hi⟩ := ih (equalBlock x b) (hx.equalBlock b)
        have hc : 0 ≤ (1 / 2 : ℝ) ^ k := pow_nonneg (by norm_num) k
        refine ⟨finProdFinEquiv (b, i), ?_⟩
        calc
          ‖x (finProdFinEquiv (b, i))‖ ≤
              (1 / 2 : ℝ) ^ k * ‖equalBlocks x b‖ := hi
          _ ≤ (1 / 2 : ℝ) ^ k * ((1 / 2 : ℝ) * ‖∑ j, x j‖) :=
            mul_le_mul_of_nonneg_left hb hc
          _ = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k * ‖∑ j, x j‖ := by ring
      rw [Nat.pow_succ' (m := M) (n := k)]
      simpa only [pow_succ'] using hstep

theorem coefficientBasic_half_gain_prefix {M : ℕ} {K : ℝ}
    (hgain : ∀ y : Fin M → E, CoefficientBasic K y →
      ∃ i, ‖y i‖ ≤ (1 / 2 : ℝ) * ‖∑ l, y l‖)
    {k j : ℕ} (hkj : M ^ k ≤ j) (x : Fin j → E)
    (hx : CoefficientBasic K x) :
    ∃ i : Fin j, i.val < M ^ k ∧
      ‖x i‖ ≤ K * (1 / 2 : ℝ) ^ k * ‖∑ l, x l‖ := by
  let e : Fin (M ^ k) ↪o Fin j :=
    OrderEmbedding.ofStrictMono (fun i => Fin.castLE hkj i) (by
      intro a b hab
      exact hab)
  obtain ⟨i, hi⟩ := coefficientBasic_half_gain_iterate hgain k
    (fun l => x (e l)) (hx.comp_orderEmbedding e)
  have hprefix_sum :
      (∑ l : Fin (M ^ k), x (e l)) =
        ∑ l : Fin j, if l.val < M ^ k then x l else 0 := by
    symm
    rw [sum_univ_eq_sum_embedding (Fin.castLEEmb hkj) _ ?_]
    · apply Finset.sum_congr rfl
      intro l _hl
      change (if l.val < M ^ k then x (e l) else 0) = x (e l)
      exact ite_eq_left l.is_lt
    · intro l hl
      have hnot : ¬ l.val < M ^ k := by
        intro hlt
        exact hl ⟨⟨l.val, hlt⟩, Fin.ext rfl⟩
      exact ite_eq_right hnot
  have hpref : ‖∑ l : Fin (M ^ k), x (e l)‖ ≤ K * ‖∑ l : Fin j, x l‖ := by
    rw [hprefix_sum]
    exact hx.norm_prefix_le (M ^ k) hkj
  have hc : 0 ≤ (1 / 2 : ℝ) ^ k := pow_nonneg (by norm_num) k
  refine ⟨e i, ?_, ?_⟩
  · change i.val < M ^ k
    exact i.is_lt
  · calc
      ‖x (e i)‖ ≤ (1 / 2 : ℝ) ^ k * ‖∑ l : Fin (M ^ k), x (e l)‖ := hi
      _ ≤ (1 / 2 : ℝ) ^ k * (K * ‖∑ l : Fin j, x l‖) :=
        mul_le_mul_of_nonneg_left hpref hc
      _ = K * (1 / 2 : ℝ) ^ k * ‖∑ l : Fin j, x l‖ := by ring

end MarkovSuperreflexivity

end OAI
