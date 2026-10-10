import OAI.Combinatorics.PolynomialVacuum.Separator.Polynomial
import OAI.Combinatorics.PolynomialVacuum.Separator.EstimateTarget

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra

noncomputable def emptySystem (n : ℕ) : System n :=
  ⟨∅, by simp [AllowedSystem]⟩

theorem system_card_zero_iff {n : ℕ} (S : System n) :
    S.val.card=0 ↔ S=emptySystem n := by
  rw [Finset.card_eq_zero]
  exact ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩

theorem separator_zero (n : ℕ) : separatorPolynomial n 0=1 := by
  rw [separatorPolynomial,tsum_eq_single (emptySystem n)]
  · simp [systemWeight,emptySystem]
  · intro S hS
    have hc : S.val.card≠0 := fun hc=>hS ((system_card_zero_iff S).mp hc)
    simp [systemWeight,zero_pow hc]

theorem separatorCoefficient_zero (n : ℕ) : separatorCoefficient n 0=1 := by
  rw [separatorCoefficient,tsum_eq_single (emptySystem n)]
  · simp [shapeWeight,emptySystem]
  · intro S hS
    have hc : S.val.card≠0 := fun hc=>hS ((system_card_zero_iff S).mp hc)
    exact ite_eq_right hc

theorem separatorPoly_natDegree_le (n : ℕ) : (separatorPoly n).natDegree≤n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

theorem separator_ofReal (n : ℕ) (hn : 1≤n) (x : ℝ) :
    separatorPolynomial n (x : ℂ)=
      ((∑k∈Finset.range (n+1), x^k*separatorCoefficient n k : ℝ) : ℂ) := by
  rw [separator_finite_power_sum n hn]
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow]

theorem separator_re_formula (n : ℕ) (hn : 1≤n) (x : ℝ) :
    (separatorPolynomial n (x : ℂ)).re=∑k∈Finset.range (n+1), x^k*separatorCoefficient n k := by
  rw [separator_ofReal n hn,Complex.ofReal_re]

theorem separator_positive_real (n : ℕ) (hn : 1≤n) (x : ℝ) (hx : 0≤x) :
    1 ≤ (separatorPolynomial n (x : ℂ)).re := by
  rw [separator_re_formula n hn]
  have h := Finset.single_le_sum (f:=fun k=>x^k*separatorCoefficient n k)
    (fun k hk=>mul_nonneg (pow_nonneg hx _) (separatorCoefficient_nonneg n k))
    (show 0∈Finset.range (n+1) by simp)
  simpa only [pow_zero,one_mul,separatorCoefficient_zero] using h

theorem separator_real_monotone (n : ℕ) (hn : 1≤n) {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    (separatorPolynomial n (x : ℂ)).re≤(separatorPolynomial n (y : ℂ)).re := by
  rw [separator_re_formula n hn,separator_re_formula n hn]
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hxy _) (separatorCoefficient_nonneg n k)

theorem separator_norm_bound (n : ℕ) (hn : 1≤n) (η : ℂ) :
    ‖separatorPolynomial n η‖≤(separatorPolynomial n (‖η‖ : ℂ)).re := by
  rw [separator_finite_power_sum n hn,separator_re_formula n hn]
  calc
    _ ≤ ∑k∈Finset.range (n+1),‖η^k*(separatorCoefficient n k : ℂ)‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (separatorCoefficient_nonneg n k)]

theorem separator_log_analyticAt_zero (n : ℕ) (hn : 1≤n) :
    AnalyticAt ℂ (fun η : ℂ=>Complex.log (separatorPolynomial n η)) 0 := by
  apply (separator_analyticAt n hn 0).clog
  simp [separator_zero]

end PolynomialVacuumCylinder

end OAI
