import OAI.NumberTheory.Ostmann.Construction.WordRangeReplay
import OAI.NumberTheory.Ostmann.Construction.WordTransferFormulaBounds

namespace OAI

/-! # Concrete complexity of all replayed intermediate range tests -/

namespace Ostmann

open scoped Classical

theorem WordRange.toHistory_cost {σ : Type*} (r : WordRange σ)
    (env : σ → HistoryFormula σ) (B C : ℕ) (hC : 1 ≤ C)
    (hr : r.word.length + 1 ≤ B) (henv : ∀ i, (env i).cost ≤ C) :
    (r.toHistory env).formula.cost ≤ C * B := by
  change (HistoryFormula.listProduct (r.word.map env)).cost ≤ C * B
  rw [HistoryFormula.cost_listProduct, List.map_map]
  have hs : (r.word.map (fun i => (env i).cost)).sum ≤ r.word.length * C := by
    induction r.word with
    | nil => simp
    | cons i is ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith [henv i]
  have hb := Nat.mul_le_mul_left C hr
  simp only [Function.comp_def]
  nlinarith

def WordRangeDecoration.WordsBounded {σ : Type*} (B : ℕ) :
    {n : ℕ} → WordRangeDecoration σ n → Prop
  | 0, .leaf ranges => ∀ r ∈ ranges, r.word.length + 1 ≤ B
  | _ + 1, .node ranges L R =>
      (∀ r ∈ ranges, r.word.length + 1 ≤ B) ∧ L.WordsBounded B ∧ R.WordsBounded B

theorem WordRangeDecoration.formulas_cost {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (env : σ → HistoryFormula σ) (B C : ℕ) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hwords : template.WordsBounded B) (hD : D.WordsBounded B)
    (henv : ∀ i, (env i).cost ≤ C) :
    ∀ r ∈ D.formulas template t ht env, r.formula.cost ≤ C * B ^ (n + 1) := by
  induction template generalizing C env with
  | leaf word =>
    cases D with
    | leaf ranges =>
      intro r hr
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      simpa only [Nat.zero_add, pow_one] using q.toHistory_cost env B C hC (hD q hq) henv
  | @node n d l r ihL ihR =>
    cases D with
    | node ranges L R =>
      let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ht.1
      have hstep : (step.formula.bind env).cost ≤ C * B := by
        apply (HistoryFormula.cost_bind_le step.formula env C hC henv).trans
        rw [HistoryPivotStep.formula_cost]
        exact Nat.mul_le_mul_left C hwords.1
      have hCB : 1 ≤ C * B := by simpa using Nat.mul_le_mul hC hB
      have hu : ∀ i, (BranchingWordHistory.updatedFormulas step env i).cost ≤ C * B := by
        intro i
        by_cases hi : i = step.target
        · subst i
          simpa only [BranchingWordHistory.updatedFormulas, Function.update_self] using hstep
        · simpa only [BranchingWordHistory.updatedFormulas, Function.update_of_ne hi] using
            (henv i).trans (by simpa using Nat.mul_le_mul_left C hB)
      have hL := ihL L t.2.1 ht.2.1 _ (C * B) hCB hwords.2.1 hD.2.1 hu
      have hR := ihR R t.2.2 ht.2.2 _ (C * B) hCB hwords.2.2 hD.2.2 hu
      have he : C * B * B ^ (n + 1) = C * B ^ (n + 1 + 1) := by rw [pow_succ]; ring
      have hb : C * B ≤ C * B ^ (n + 1 + 1) := by
        apply Nat.mul_le_mul_left C
        simpa only [pow_one] using
          (show B ^ 1 ≤ B ^ (n + 1 + 1) from Nat.pow_le_pow_right hB (by omega))
      intro q hq
      change q ∈ ranges.map (fun q => q.toHistory env) ++ _ at hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨q0, hq0, heq⟩ := List.mem_map.mp hq
        rw [← heq]
        exact (q0.toHistory_cost env B C hC (hD.1 q0 hq0) henv).trans hb
      · rcases List.mem_append.mp hq with hq | hq
        · exact (hL q hq).trans_eq he
        · exact (hR q hq).trans_eq he

def WordRangeDecoration.CountBounded {σ : Type*} (K : ℕ) :
    {n : ℕ} → WordRangeDecoration σ n → Prop
  | 0, .leaf ranges => ranges.length ≤ K
  | _ + 1, .node ranges L R => ranges.length ≤ K ∧ L.CountBounded K ∧ R.CountBounded K

theorem WordRangeDecoration.count_le {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (K : ℕ) (hD : D.CountBounded K) :
    D.count ≤ K * (2 ^ (n + 1) - 1) := by
  induction D with
  | leaf ranges => simpa only [count, CountBounded, Nat.zero_add, pow_one, Nat.reduceSub, Nat.mul_one] using hD
  | @node n ranges L R ihL ihR =>
    have hL := ihL hD.2.1
    have hR := ihR hD.2.2
    have hp := Nat.one_le_two_pow (n := n + 1)
    change ranges.length + L.count + R.count ≤ K * (2 ^ (n + 1 + 1) - 1)
    rw [pow_succ]
    have he : 2 ^ (n + 1) * 2 - 1 = (2 ^ (n + 1) - 1) * 2 + 1 := by omega
    rw [he]
    nlinarith only [hD.1, hL, hR]

end Ostmann

end OAI
