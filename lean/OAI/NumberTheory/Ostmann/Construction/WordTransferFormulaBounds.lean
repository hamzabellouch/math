import OAI.NumberTheory.Ostmann.Construction.WordTransferCounts

namespace OAI

/-! # Derived polynomial sizes for the concrete fixed-depth word transfer -/

namespace Ostmann.WordTransferTemplate

open scoped Classical

variable {σ : Type*}

def WordsBounded (B : ℕ) : {n : ℕ} → WordTransferTemplate σ n → Prop
  | 0, .leaf word => word.length + 1 ≤ B
  | _ + 1, .node d l r => d.left.length + d.right.length + 4 ≤ B ∧
      l.WordsBounded B ∧ r.WordsBounded B

/-- Every output formula is obtained by at most n substitutions, each of
size at most B. This supplies the polynomial loss used by the analytic bound. -/
theorem branching_formula_cost {n : ℕ} (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t)
    (B C : ℕ) (hB : 1 ≤ B) (hC : 1 ≤ C) (hwords : template.WordsBounded B)
    (env : σ → HistoryFormula σ) (henv : ∀ i, (env i).cost ≤ C) :
    (∀ z ∈ (template.branching t hn).formulaLeaves env, z.2.cost ≤ C * B ^ (n + 1)) ∧
    (∀ F ∈ (template.branching t hn).pivotFormulas env, F.cost ≤ C * B ^ (n + 1)) := by
  induction template generalizing C env with
  | leaf word =>
    constructor
    · intro z hz
      simp only [branching, BranchingWordHistory.formulaLeaves, List.mem_singleton] at hz
      subst z
      simp only [HistoryFormula.cost_listProduct, List.map_map, Function.comp_def, Nat.zero_add, pow_one]
      have hsum : (word.map (fun i => (env i).cost)).sum ≤ word.length * C := by
        clear hwords
        induction word with
        | nil => simp
        | cons i word ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          exact (Nat.add_le_add (henv i) ih).trans_eq (by ring)
      have hlen : word.length + 1 ≤ B := hwords
      have hb := Nat.mul_le_mul_left C hlen
      nlinarith
    · intro F hF
      simp only [branching, BranchingWordHistory.pivotFormulas, List.not_mem_nil] at hF
  | @node n d l r hl hr =>
    let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hn.1
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
    obtain ⟨hll, hlp⟩ := hl t.2.1 hn.2.1 (C * B) hCB hwords.2.1
      (BranchingWordHistory.updatedFormulas step env) hu
    obtain ⟨hrl, hrp⟩ := hr t.2.2 hn.2.2 (C * B) hCB hwords.2.2
      (BranchingWordHistory.updatedFormulas step env) hu
    have heq : C * B * B ^ (n + 1) = C * B ^ (n + 1 + 1) := by rw [pow_succ]; ring
    have hroot : C * B ≤ C * B ^ (n + 1 + 1) := by
      apply Nat.mul_le_mul_left C
      calc
        B = B ^ 1 := by simp
        _ ≤ _ := Nat.pow_le_pow_right hB (by omega)
    constructor
    · intro z hz
      change z ∈ (l.branching t.2.1 hn.2.1).formulaLeaves (BranchingWordHistory.updatedFormulas step env) ++
        ((r.branching t.2.2 hn.2.2).formulaLeaves (BranchingWordHistory.updatedFormulas step env)).map
          BranchingWordHistory.flipSigned at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact (hll z hz).trans_eq heq
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
        exact (hrl w hw).trans_eq heq
    · intro F hF
      change F ∈ step.formula.bind env ::
        ((l.branching t.2.1 hn.2.1).pivotFormulas (BranchingWordHistory.updatedFormulas step env) ++
          (r.branching t.2.2 hn.2.2).pivotFormulas (BranchingWordHistory.updatedFormulas step env)) at hF
      rcases List.mem_cons.mp hF with rfl | hF
      · exact hstep.trans hroot
      · rcases List.mem_append.mp hF with hF | hF
        · exact (hlp F hF).trans_eq heq
        · exact (hrp F hF).trans_eq heq

end Ostmann.WordTransferTemplate

end OAI
