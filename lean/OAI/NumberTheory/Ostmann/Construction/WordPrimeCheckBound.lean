import OAI.NumberTheory.Ostmann.Construction.WordPrimeBounds
import OAI.NumberTheory.Ostmann.Arithmetic.ReconstructedCoprimalityBound
import OAI.NumberTheory.Ostmann.Construction.GroupedScheduleCoefficient

namespace OAI

/-! # Original-prior cancellation retains every reconstructed prime check -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def WordPrimeDecoration.checkAt {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (i : Fin D.count) : HistoryPrimeCheck σ V :=
  (D.checks template t ht .prime)[i.val]'(by rw [D.checks_length]; exact i.isLt)

theorem WordPrimeDecoration.checkAt_mem {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (i : Fin D.count) :
    D.checkAt template t ht i ∈ D.checks template t ht .prime := List.getElem_mem _

theorem WordPrimeDecoration.checkAt_all {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (a : σ → ℤ) (prime : V → ℕ) :
    (∀ i, (D.checkAt template t ht i).Holds a prime) ↔
      ∀ g ∈ D.checks template t ht .prime, g.Holds a prime := by
  constructor
  · intro h g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    have hi' : i < D.count := by rwa [D.checks_length] at hi
    exact h ⟨i, hi'⟩
  · intro h i
    exact h _ (D.checkAt_mem template t ht i)

/-- `W` may already contain the other history, all range/unit gates and the
graph phase. Its support supplies the literal validity of this history.
The right side uses the derived number and degree of the prime checks. -/
theorem word_prime_checks_bound
    {A : Type*} [Fintype A] [Nonempty A] {m n : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (D : WordPrimeDecoration (Fin (m + 1)) n)
    (template : WordTransferTemplate (ExpandedScheduledVariable (Fin (m + 1)) n) n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B)
    (μ : Fin (m + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α β V R : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ i a, μ i a ≤ β)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hsmall : ∀ a, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < prime a)
    (W : (Fin (m + 1) → A) → ℂ) (C δ : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hW : ∀ x, ‖W x‖ ≤ C)
    (hvalid : ∀ x, W x ≠ 0 → ValidTransferHistory
      (wordTransferSystem (ExpandedScheduledVariable (Fin (m + 1)) n)) n
      (template.state (expandedPrimeNatValues n (fun i => prime (x i)))) t)
    (hcancel : ‖∑ x, (productPrior μ x : ℂ) * W x‖ ≤ δ) :
    ‖∑ x, (productPrior μ x : ℂ) *
      (if ∀ g ∈ D.checks template t ht .prime,
          g.Holds (expandedPrimeValues n (fun i => (prime (x i) : ℤ))) (fun i => prime (x i))
        then W x else 0)‖ ≤
      δ + C * (D.count : ℝ) * (B ^ (n + 1) : ℕ) * (α + Real.log R / V * β) := by
  let G := D.checkAt template t ht
  let F := fun i => (G i).formula.originalPrimes
  let coord := fun i => (G i).coordinate
  let y := fun i (x : Fin (m + 1) → A) =>
    (G i).formula.integerValue (expandedPrimeValues n (fun k => (prime (x k) : ℤ)))
  have hmem i := D.checkAt_mem template t ht i
  have hinputs i : (F i).InputsBounded R :=
    (G i).formula.originalPrimes_inputs R (by linarith)
      (template.pivot_inputsBounded t ht R (by linarith) hfreq .prime (fun _ => trivial)
        _ (D.check_formula_mem template t ht .prime _ (hmem i)))
  have hv (x : Fin (m + 1) → A) (hw : W x ≠ 0) (i : Fin D.count) :
      (F i).value (fun k => (prime (x k) : ℚ)) = y i x ∧
        ¬prime (x (coord i)) ∣ (F i).cleared.denominator.natAbs := by
    constructor
    · have hi := D.check_integer_value template t ht
        (expandedPrimeNatValues n (fun k => prime (x k))) (hvalid x hw) _ (hmem i)
      rw [expandedPrimeNatValues_cast] at hi
      have hq : (fun k => (expandedPrimeNatValues n (fun j => prime (x j)) k : ℚ)) =
          (fun k => (expandedPrimeValues n (fun j => (prime (x j) : ℤ)) k : ℚ)) := by
        funext k
        cases k <;> rfl
      rw [hq] at hi
      exact ((G i).formula.originalPrimes_value _).trans hi
    · have hd := D.check_denominator template t ht B hB hwords _ (hmem i)
      have hdN : (G i).formula.cleared.denominator.natAbs ∣ wordTransferFullPeriod n t B := by
        simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
      have hp := prime_coprime_wordTransferFullPeriod n t B (prime (x (coord i)))
        (hprime _) (hsmall _)
      change ¬prime (x (coord i)) ∣ (G i).formula.originalPrimes.cleared.denominator.natAbs
      rw [HistoryFormula.originalPrimes_denominator]
      exact (hprime _).coprime_iff_not_dvd.mp (hp.of_dvd_right hdN)
  have hh := reconstructed_coprimality_bound prime hpInj hprime F coord y μ hμ hmass
    α V R (fun _ => β) hα (fun _ => hβ) hV hR hmax
    (fun i a => hpmax (coord i) a) hlower hupper hinputs W C δ hC hδ hW hv hcancel
  have he (x : Fin (m + 1) → A) :
      (∀ i, (prime (x (coord i))).Coprime (y i x).natAbs) ↔
        ∀ g ∈ D.checks template t ht .prime,
          g.Holds (expandedPrimeValues n (fun k => (prime (x k) : ℤ))) (fun k => prime (x k)) := by
    simpa only [G, coord, y, HistoryPrimeCheck.Holds] using
      D.checkAt_all template t ht (expandedPrimeValues n (fun k => (prime (x k) : ℤ)))
        (fun k => prime (x k))
  simp_rw [he] at hh
  apply hh.trans
  apply add_le_add le_rfl
  have hnonneg : 0 ≤ α + Real.log R / V * β :=
    add_nonneg hα (mul_nonneg (div_nonneg (Real.log_nonneg (by linarith)) hV.le) hβ)
  have hs : (∑ i : Fin D.count, ((F i).cost : ℝ) * (α + Real.log R / V * β)) ≤
      (D.count : ℝ) * (B ^ (n + 1) : ℕ) * (α + Real.log R / V * β) := by
    calc
      _ ≤ ∑ _i : Fin D.count, (B ^ (n + 1) : ℕ) * (α + Real.log R / V * β) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ hnonneg
        exact_mod_cast (show (F i).cost ≤ B ^ (n + 1) by
          rw [HistoryFormula.originalPrimes_cost]
          exact D.check_cost template t ht B hB hwords _ (hmem i))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; ring
  exact (mul_le_mul_of_nonneg_left hs hC).trans_eq (by ring)

end Ostmann

end OAI
