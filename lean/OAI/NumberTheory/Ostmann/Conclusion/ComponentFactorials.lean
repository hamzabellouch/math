import OAI.NumberTheory.Ostmann.Conclusion.OverlapComponents

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Conclusion

theorem factorial_mul_le_exp (a m : ℕ) (ha : 0 < a) :
    ((a*m).factorial : ℝ) ≤ (m.factorial : ℝ)^a *
      Real.exp ((m : ℝ)*(a : ℝ)*Real.log a) := by
  have h : ((a*m).factorial : ℝ) ≤ (m.factorial : ℝ)^a * (a : ℝ)^(a*m) := by
    exact_mod_cast factorial_mul_le a m
  have he : Real.exp ((m : ℝ)*(a : ℝ)*Real.log a) = (a : ℝ)^(a*m) := by
    rw [show (m : ℝ)*(a : ℝ)*Real.log a = (a*m : ℕ)*Real.log a by push_cast; ring]
    rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast ha)]
  rw [he]
  exact h

theorem component_log_sum_bound {ι : Type*} [Fintype ι] (a : ι → ℕ) {r : ℕ}
    (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = r) :
    ∑ i, (a i : ℝ)*Real.log (a i) ≤
      ((r : ℝ)-Fintype.card ι)*(Real.log r+1) := by
  have hr : (∑ i, (a i : ℝ)) = (r : ℝ) := by exact_mod_cast hsum
  calc
    _ ≤ ∑ i, ((a i : ℝ)-1)*(Real.log r+1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hai : a i ≤ r := by
        rw [← hsum]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      exact component_log_bound (by exact_mod_cast ha i) (by exact_mod_cast hai)
    _ = ((r : ℝ)-Fintype.card ι)*(Real.log r+1) := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, hr]
      simp

theorem component_factorial_product_bound {ι : Type*} [Fintype ι] (a : ι → ℕ)
    {r : ℕ} (m : ℕ) (ha : ∀ i, 0 < a i) (hsum : ∑ i, a i = r) :
    (∏ i, ((a i*m).factorial : ℝ)) ≤ (m.factorial : ℝ)^r *
      Real.exp ((m : ℝ)*((r : ℝ)-Fintype.card ι)*(Real.log r+1)) := by
  calc
    _ ≤ ∏ i, ((m.factorial : ℝ)^(a i) *
        Real.exp ((m : ℝ)*(a i : ℝ)*Real.log (a i))) := by
      apply Finset.prod_le_prod₀
      · intro i hi; positivity
      · intro i hi; exact factorial_mul_le_exp (a i) m (ha i)
    _ = (m.factorial : ℝ)^r * Real.exp ((m : ℝ)*∑ i, (a i : ℝ)*Real.log (a i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum, ← Real.exp_sum]
      congr 2
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (component_log_sum_bound a ha hsum)
        (show 0 ≤ (m : ℝ) by positivity)
      nlinarith

theorem bad_component_factorial_bound {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m))
    (hr : 0 < r) (hbad : BadArrangement σ) :
    (∏ i : OverlapComponent σ,
      ((Fintype.card {a // leftComponent σ a = i}*m).factorial : ℝ)) ≤
      (m.factorial : ℝ)^r * Real.exp ((Real.log r+1)*(r : ℝ)*m/4) := by
  refine (component_factorial_product_bound _ m (component_card_pos σ)
    (component_cards_sum σ)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hbadR : 3*(r : ℝ) < 4*Fintype.card (OverlapComponent σ) := by
    exact_mod_cast hbad
  have hlog : 0 ≤ Real.log (r : ℝ)+1 := by
    have := Real.log_nonneg (by exact_mod_cast hr : (1 : ℝ) ≤ r)
    linarith
  have hweight : 0 ≤ (m : ℝ)*(Real.log r+1) := mul_nonneg (by positivity) hlog
  nlinarith

end Ostmann.Conclusion

end

end OAI
