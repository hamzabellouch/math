import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-! # Factorial costs of components in the arrangement graph -/

namespace Ostmann

open scoped BigOperators

/-- Assigning a*m labeled positions to a blocks gives the factorial
inequality used in the count of bad arrangements. -/
theorem component_factorial_le (a m : ℕ) :
    (a * m).factorial ≤ m.factorial ^ a * a ^ (a * m) := by
  classical
  let s : Finset (Fin a) := Finset.univ
  let f : Fin a → ℕ := fun _ => m
  have hmem : f ∈ Finset.piAntidiag s (a * m) := by
    simp [Finset.mem_piAntidiag, s, f]
  have hsum : a ^ (a * m) =
      ∑ k ∈ s.piAntidiag (a * m), Nat.multinomial s k := by
    simpa [s] using
      (Finset.sum_pow_eq_sum_piAntidiag (R := ℕ) s (fun _ => (1 : ℕ)) (a * m))
  have hb := Finset.single_le_sum (fun k (_ : k ∈ Finset.piAntidiag s (a * m)) =>
    Nat.zero_le (Nat.multinomial s k)) hmem
  rw [← hsum] at hb
  have hs := Nat.multinomial_spec s f
  simp only [s, f, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_const, smul_eq_mul] at hs
  rw [← hs]
  exact Nat.mul_le_mul_left _ hb

theorem component_log_cost (a r : ℝ) (ha : 1 ≤ a) (har : a ≤ r) :
    a * Real.log a ≤ (a - 1) * (Real.log r + 1) := by
  have ha0 : 0 < a := by linarith
  have hlog : Real.log a ≤ Real.log r := Real.log_le_log ha0 har
  have hlog' : Real.log a ≤ a - 1 := Real.log_le_sub_one_of_pos ha0
  have hm := mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr ha)
  nlinarith

/-- The sum of a-1 is exactly the number of leaves minus the number
of components, so the entropy cost is controlled by this deficit. -/
theorem component_entropy_bound {I : Type*} [Fintype I]
    (a : I → ℕ) (r : ℕ) (ha : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = r) :
    (∑ i, (a i : ℝ) * Real.log (a i)) ≤
      ((r : ℝ) - Fintype.card I) * (Real.log r + 1) := by
  have hle (i : I) : a i ≤ r := by
    rw [← hsum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hcost (i : I) := component_log_cost (a i) r
    (by exact_mod_cast ha i) (by exact_mod_cast hle i)
  calc
    _ ≤ ∑ i, ((a i : ℝ) - 1) * (Real.log r + 1) := Finset.sum_le_sum fun i _ => hcost i
    _ = ((∑ i, (a i : ℝ)) - Fintype.card I) * (Real.log r + 1) := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    _ = _ := by rw [← Nat.cast_sum, hsum]

/-- Product of the component assignment counts, with the cost expressed
through the deficit in the number of components. -/
theorem component_factorial_product_bound {I : Type*} [Fintype I]
    (a : I → ℕ) (r m : ℕ) (ha : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = r) :
    (∏ i, ((a i * m).factorial : ℝ)) ≤
      (m.factorial : ℝ) ^ r *
        Real.exp ((m : ℝ) * ((r : ℝ) - Fintype.card I) * (Real.log r + 1)) := by
  classical
  have hp (i : I) : (a i : ℝ) ^ (a i * m) =
      Real.exp ((m : ℝ) * ((a i : ℝ) * Real.log (a i))) := by
    have hi : 0 < (a i : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (ha i)
    rw [show (m : ℝ) * ((a i : ℝ) * Real.log (a i)) =
      ((a i * m : ℕ) : ℝ) * Real.log (a i) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log hi]
  calc
    _ ≤ ∏ i, (m.factorial : ℝ) ^ a i * (a i : ℝ) ^ (a i * m) := by
      exact_mod_cast (Finset.prod_le_prod (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
        component_factorial_le (a i) m))
    _ = (m.factorial : ℝ) ^ r * Real.exp ((m : ℝ) * ∑ i, (a i : ℝ) * Real.log (a i)) := by
      simp_rw [hp]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum,
        ← Real.exp_sum, ← Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (component_entropy_bound a r ha hsum) (show 0 ≤ (m : ℝ) by positivity)

end Ostmann

end OAI
