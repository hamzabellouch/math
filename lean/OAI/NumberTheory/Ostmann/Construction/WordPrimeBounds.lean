import OAI.NumberTheory.Ostmann.Construction.WordPrimeReplay
import OAI.NumberTheory.Ostmann.Construction.WordTransferFullPeriod
import OAI.NumberTheory.Ostmann.Arithmetic.ReconstructedWordQueries

namespace OAI

/-! # Derived size, integrality and denominator bounds for the prime checks -/

namespace Ostmann

open scoped Classical

theorem WordPrimeDecoration.check_cost {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) :
    ∀ g ∈ D.checks template t ht .prime, g.formula.cost ≤ B ^ (n + 1) := by
  intro g hg
  simpa only [Nat.one_mul] using
    (template.branching_formula_cost t ht B 1 hB le_rfl hwords .prime (fun _ => le_rfl)).2
      g.formula (D.check_formula_mem template t ht .prime g hg)

theorem WordPrimeDecoration.check_denominator {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) :
    ∀ g ∈ D.checks template t ht .prime,
      g.formula.cleared.denominator ∣ (wordTransferFullPeriod n t B : ℤ) := by
  intro g hg
  have hd := (template.branching_denominator_period t ht B hB hwords 1 (one_dvd _)).2
    g.formula (D.check_formula_mem template t ht .prime g hg)
  simp only [mul_one] at hd
  exact hd.trans (by
    rw [wordTransferFullPeriod, Nat.cast_mul]
    exact dvd_mul_right _ _)

theorem WordPrimeDecoration.check_integer_value {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (x : σ → ℕ) (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    ∀ g ∈ D.checks template t ht .prime,
      g.formula.value (fun i => (x i : ℚ)) = g.formula.integerValue (fun i => (x i : ℤ)) := by
  intro g hg
  have hi := (BranchingWordHistory.pivotFormulas_integral_iff (template.branching t ht)
    .prime (fun i => (x i : ℤ)) (fun i => (x i : ℤ))
    (by intro i; simp only [HistoryFormula.value_prime])).mpr
      (template.branching_valid x t ht hv)
  obtain ⟨z, hz⟩ := hi g.formula (D.check_formula_mem template t ht .prime g hg)
  rw [g.formula.integerValue_of_value _ z hz]
  simpa only [Int.cast_natCast] using hz

theorem WordTransferTemplate.pivot_inputsBounded {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (R : ℝ) (hR : 1 ≤ R)
    (hf : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (env : σ → HistoryFormula σ) (henv : ∀ i, (env i).InputsBounded R) :
    ∀ F ∈ (template.branching t ht).pivotFormulas env, F.InputsBounded R := by
  induction template generalizing env with
  | leaf word => simp only [branching, BranchingWordHistory.pivotFormulas,
      List.not_mem_nil, false_implies, implies_true]
  | @node n d l r ihL ihR =>
    let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ht.1
    have hs : step.formula.InputsBounded R := step.formula_inputsBounded R hR
      (hf _ (List.mem_cons_of_mem _ (List.mem_append_left _ (frequencyRoot_mem_allFrequencyList n t.2.1))))
      (hf _ (List.mem_cons_of_mem _ (List.mem_append_right _ (frequencyRoot_mem_allFrequencyList n t.2.2))))
      (hf _ (List.mem_cons_self ..))
    have hp := step.formula.inputsBounded_bind env R hs henv
    have hu : ∀ i, (BranchingWordHistory.updatedFormulas step env i).InputsBounded R := by
      intro i
      by_cases hi : i = step.target
      · subst i
        simpa only [BranchingWordHistory.updatedFormulas, Function.update_self] using hp
      · simpa only [BranchingWordHistory.updatedFormulas, Function.update_of_ne hi] using henv i
    have hl := ihL t.2.1 ht.2.1
      (fun s hs => hf s (List.mem_cons_of_mem _ (List.mem_append_left _ hs))) _ hu
    have hr := ihR t.2.2 ht.2.2
      (fun s hs => hf s (List.mem_cons_of_mem _ (List.mem_append_right _ hs))) _ hu
    intro F hF
    change F ∈ step.formula.bind env :: (_ ++ _) at hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hp
    · rcases List.mem_append.mp hF with hF | hF
      · exact hl F hF
      · exact hr F hF

def WordPrimeDecoration.CountBounded {V : Type*} (K : ℕ) :
    {n : ℕ} → WordPrimeDecoration V n → Prop
  | 0, .leaf => True
  | _ + 1, .node coordinates L R =>
      coordinates.length ≤ K ∧ L.CountBounded K ∧ R.CountBounded K

theorem WordPrimeDecoration.count_le {V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (K : ℕ) (hD : D.CountBounded K) :
    D.count ≤ K * (2 ^ n - 1) := by
  induction D with
  | leaf => simp only [count, pow_zero, Nat.sub_self, Nat.mul_zero, le_refl]
  | @node n coordinates L R ihL ihR =>
    have hL := ihL hD.2.1
    have hR := ihR hD.2.2
    have hp := Nat.one_le_two_pow (n := n)
    change coordinates.length + L.count + R.count ≤ K * (2 ^ (n + 1) - 1)
    rw [pow_succ]
    have he : 2 ^ n * 2 - 1 = (2 ^ n - 1) * 2 + 1 := by omega
    rw [he]
    nlinarith only [hD.1, hL, hR]

end Ostmann

end OAI
