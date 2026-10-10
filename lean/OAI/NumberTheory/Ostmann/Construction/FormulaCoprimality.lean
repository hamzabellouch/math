import OAI.NumberTheory.Ostmann.Construction.HistoryFormula

namespace OAI

/-! # The coprimality error with constructed history degree and value budgets -/

namespace Ostmann

open scoped BigOperators Classical

theorem formula_coprimality_removal {A I : Type*} [Fintype A] [Nonempty A] [Fintype I]
    {n : ℕ} (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (F : I → HistoryFormula (Fin (n + 1))) (coord : I → Fin (n + 1))
    (hzero : ∀ j, zeroHistoryVariable (coord j) (F j).cleared.numerator ≠ 0)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α V R : ℝ) (β : I → ℝ) (hα : 0 ≤ α) (hβ : ∀ j, 0 ≤ β j)
    (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ j a, μ (coord j) a ≤ β j)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hinputs : ∀ j, (F j).InputsBounded R)
    (W : (Fin (n + 1) → A) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hW : ∀ x, ‖W x‖ ≤ B) :
    ‖(∑ x, (productPrior μ x : ℂ) *
        (if ∀ j, ¬prime (x (coord j)) ∣
          (integerTestValue (fun a => (prime a : ℤ)) (F j).cleared.numerator x).natAbs
          then W x else 0)) - ∑ x, (productPrior μ x : ℂ) * W x‖ ≤
      B * ∑ j, ((F j).cost : ℝ) * (α + Real.log R / V * β j) := by
  have hvalue (j : I) (x : Fin (n + 1) → A) :
      |(integerTestValue (fun a => (prime a : ℤ))
        (zeroHistoryVariable (coord j) (F j).cleared.numerator) x : ℝ)| ≤ R ^ (F j).cost := by
    apply (F j).zero_variable_bound (coord j) (fun i => (prime (x i) : ℤ)) R hR _ (hinputs j)
    intro i
    simpa only [Int.cast_natCast,
      abs_of_nonneg (show (0 : ℝ) ≤ prime (x i) from Nat.cast_nonneg _)] using hupper (x i)
  have hh := history_coprimality_removal prime hpInj hprime
    (fun j => (F j).cleared.numerator) coord hzero μ hμ hmass α V β
    (fun j => R ^ (F j).cost) hα hβ hV
    (fun j => one_le_pow₀ (by linarith : (1 : ℝ) ≤ R)) hmax hpmax hlower hvalue W B hB hW
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hB
  apply Finset.sum_le_sum
  intro j _
  have hd : ((F j).cleared.numerator.totalDegree : ℝ) ≤ (F j).cost := by
    exact_mod_cast (F j).degree_le_cost
  rw [Real.log_pow]
  have hdeg := mul_le_mul_of_nonneg_right hd hα
  calc
    _ ≤ ((F j).cost : ℝ) * α + ((F j).cost : ℝ) * Real.log R / V * β j :=
      add_le_add hdeg le_rfl
    _ = _ := by ring

end Ostmann

end OAI
