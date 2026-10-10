import OAI.NumberTheory.Ostmann.Construction.FixedPivotFormulas
import OAI.NumberTheory.Ostmann.Construction.FiniteReconstructedCoprimality
import OAI.NumberTheory.Ostmann.Construction.WordPrimeCheckBound

namespace OAI

/-! # Reconstructed prime checks with a fixed external integer coordinate -/

namespace Ostmann

open scoped BigOperators Classical

def fixedPivotPrimeValues {V : Type*} (M : ℕ) (p : V → ℕ) : Option V → ℕ
  | none => M
  | some i => p i

theorem word_prime_checks_fixed_pivot_bound
    {A : Type*} [Fintype A] [Nonempty A] {K : Type*} [Fintype K] [Nonempty K] {n : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (D : WordPrimeDecoration (Option (K)) n)
    (template : WordTransferTemplate (ExpandedScheduledVariable (Option (K)) n) n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (coord : Fin D.count → K)
    (hcoord : ∀ i, (D.checkAt template t ht i).coordinate = some (coord i))
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (M : ℕ)
    (μ : K → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α β V R : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V) (hR : 3 ≤ R)
    (hM : (M : ℝ) ≤ R)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ i a, μ i a ≤ β)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hsmall : ∀ a, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < prime a)
    (W : (K → A) → ℂ) (C δ : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hW : ∀ x, ‖W x‖ ≤ C)
    (hvalid : ∀ x, W x ≠ 0 → ValidTransferHistory
      (wordTransferSystem (ExpandedScheduledVariable (Option (K)) n)) n
      (template.state (expandedPrimeNatValues n (fixedPivotPrimeValues M (fun i => prime (x i))))) t)
    (hcancel : ‖∑ x, (finiteProductPrior μ x : ℂ) * W x‖ ≤ δ) :
    ‖∑ x, (finiteProductPrior μ x : ℂ) *
      (if ∀ g ∈ D.checks template t ht .prime,
          g.Holds (expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => prime (x j)) i : ℤ)))
            (fixedPivotPrimeValues M (fun i => prime (x i))) then W x else 0)‖ ≤
      δ + C * (D.count : ℝ) * (B ^ (n + 1) : ℕ) * (α + Real.log R / V * β) := by
  let G := D.checkAt template t ht
  let F := fun i => (G i).formula.fixedOriginalPrimes (M : ℤ)
  let q := fun x : K → A => fixedPivotPrimeValues M (fun i => prime (x i))
  let a := fun x => expandedPrimeValues n (fun i => (q x i : ℤ))
  let y := fun i x => (G i).formula.integerValue (a x)
  have hmem i := D.checkAt_mem template t ht i
  have hinputs i : (F i).InputsBounded R := by
    apply (G i).formula.fixedOriginalPrimes_inputs (M : ℤ) R (by linarith)
      (by simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ (M : ℝ) from Nat.cast_nonneg M)] using hM)
    exact template.pivot_inputsBounded t ht R (by linarith) hfreq .prime (fun _ => trivial)
      _ (D.check_formula_mem template t ht .prime _ (hmem i))
  have hv (x : K → A) (hw : W x ≠ 0) (i : Fin D.count) :
      (F i).value (fun k => (prime (x k) : ℚ)) = y i x ∧
        ¬prime (x (coord i)) ∣ (F i).cleared.denominator.natAbs := by
    constructor
    · have hi := D.check_integer_value template t ht
        (expandedPrimeNatValues n (q x)) (hvalid x hw) _ (hmem i)
      rw [expandedPrimeNatValues_cast] at hi
      have hq : (fun k => (expandedPrimeNatValues n (q x) k : ℚ)) =
          (fun k => (a x k : ℚ)) := by
        funext k
        cases k <;> rfl
      rw [hq] at hi
      have he := (G i).formula.fixedOriginalPrimes_value (M : ℤ) (fun k => (prime (x k) : ℤ))
      apply he.trans
      have hcast : (fun k => (q x k : ℤ)) =
          (fun k => match k with | none => (M : ℤ) | some j => (prime (x j) : ℤ)) := by
        funext k
        cases k <;> rfl
      change (G i).formula.value (fun k => (a x k : ℚ)) = (y i x : ℚ) at hi
      dsimp only [a] at hi
      rw [hcast] at hi
      exact hi
    · have hd := D.check_denominator template t ht B hB hwords _ (hmem i)
      have hdN : (G i).formula.cleared.denominator.natAbs ∣ wordTransferFullPeriod n t B := by
        simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
      have hp := prime_coprime_wordTransferFullPeriod n t B (prime (x (coord i)))
        (hprime _) (hsmall _)
      change ¬prime (x (coord i)) ∣ ((G i).formula.fixedOriginalPrimes (M : ℤ)).cleared.denominator.natAbs
      rw [HistoryFormula.fixedOriginalPrimes_denominator]
      exact (hprime _).coprime_iff_not_dvd.mp (hp.of_dvd_right hdN)
  have hh := finite_reconstructed_coprimality_bound prime hpInj hprime F coord y μ hμ hmass
    α V R (fun _ => β) hα (fun _ => hβ) hV hR hmax
    (fun i a => hpmax (coord i) a) hlower hupper hinputs W C δ hC hδ hW hv hcancel
  have he (x : K → A) :
      (∀ i, (prime (x (coord i))).Coprime (y i x).natAbs) ↔
        ∀ g ∈ D.checks template t ht .prime, g.Holds (a x) (q x) := by
    rw [← D.checkAt_all template t ht (a x) (q x)]
    apply forall_congr'
    intro i
    change (prime (x (coord i))).Coprime (y i x).natAbs ↔
      (q x ((G i).coordinate)).Coprime (y i x).natAbs
    rw [hcoord]
    rfl
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
          rw [HistoryFormula.fixedOriginalPrimes_cost]
          exact D.check_cost template t ht B hB hwords _ (hmem i))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  exact (mul_le_mul_of_nonneg_left hs hC).trans_eq (by ring)

end Ostmann

end OAI
