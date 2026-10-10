import OAI.Combinatorics.PolynomialVacuum.Separator.Summability

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra

noncomputable def shapeWeight {n : ℕ} (S : System n) : ℝ :=
  PolynomialVacuumBridge.Corridor.criticalActivity^(∑ P∈S.val,P.vertices.card)

noncomputable def separatorCoefficient (n k : ℕ) : ℝ :=
  ∑' S : System n, if S.val.card=k then shapeWeight S else 0

noncomputable def separatorPoly (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n+1), Polynomial.monomial k (separatorCoefficient n k : ℂ)

theorem shapeWeight_pos {n : ℕ} (S : System n) : 0 < shapeWeight S :=
  pow_pos PolynomialVacuumBridge.Corridor.criticalActivity_pos _

theorem systemWeight_shape {n : ℕ} (η : ℂ) (S : System n) :
    systemWeight η S=η^S.val.card*(shapeWeight S : ℂ) := by
  simp only [systemWeight,shapeWeight,criticalActivity_xStar,Complex.ofReal_pow]

theorem shapeWeight_summable (n : ℕ) (hn : 1 ≤ n) : Summable (shapeWeight (n:=n)) := by
  apply Complex.summable_ofReal.mp
  apply (separator_systems_summable n hn 1).congr
  intro S
  simp only [systemWeight_shape,one_pow,one_mul]

theorem separatorCoefficient_summable (n k : ℕ) (hn : 1 ≤ n) :
    Summable (fun S : System n => if S.val.card=k then shapeWeight S else 0) := by
  apply ((shapeWeight_summable n hn).indicator {S : System n | S.val.card=k}).congr
  intro S
  simp only [Set.indicator_apply,Set.mem_ofPred_eq]

theorem separatorCoefficient_nonneg (n k : ℕ) : 0 ≤ separatorCoefficient n k := by
  apply tsum_nonneg
  intro S
  split_ifs
  · exact (shapeWeight_pos S).le
  · rfl

theorem separator_finite_power_sum (n : ℕ) (hn : 1 ≤ n) (η : ℂ) :
    separatorPolynomial n η=∑ k ∈ Finset.range (n+1),
      η^k*(separatorCoefficient n k : ℂ) := by
  have hterm : ∀ S : System n, systemWeight η S=
      ∑ k ∈ Finset.range (n+1),η^k*(if S.val.card=k then (shapeWeight S : ℂ) else 0) := by
    intro S
    rw [Finset.sum_eq_single S.val.card]
    · simp [systemWeight_shape]
    · intro k hk hne
      simp [Ne.symm hne]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le (separated_system_card_le n S)))).elim
  simp only [separatorPolynomial,hterm]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [tsum_mul_left]
    congr 1
    rw [separatorCoefficient,Complex.ofReal_tsum]
    apply tsum_congr
    intro S
    split_ifs <;> simp
  · intro k hk
    apply Summable.mul_left
    have h := Complex.summable_ofReal.mpr (separatorCoefficient_summable n k hn)
    simpa only [apply_ite,Complex.ofReal_zero] using h

theorem separatorPoly_eval (n : ℕ) (hn : 1 ≤ n) (η : ℂ) :
    (separatorPoly n).eval η=separatorPolynomial n η := by
  rw [separator_finite_power_sum n hn η,separatorPoly,Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [mul_comm]

theorem separator_analyticAt (n : ℕ) (hn : 1 ≤ n) (η : ℂ) :
    AnalyticAt ℂ (separatorPolynomial n) η := by
  have heq : separatorPolynomial n=fun z =>∑ k ∈ Finset.range (n+1),
      z^k*(separatorCoefficient n k : ℂ) := funext (separator_finite_power_sum n hn)
  rw [heq]
  apply Finset.analyticAt_fun_sum
  intro k hk
  fun_prop

end PolynomialVacuumCylinder

end OAI
