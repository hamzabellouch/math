import OAI.Combinatorics.PolynomialVacuum.Algebra.Scalars

namespace OAI

namespace PolynomialVacuumAlgebra

@[simp] theorem spin_zero_ne_plus : Spin.zero ≠ Spin.plus := by decide
@[simp] theorem spin_zero_ne_minus : Spin.zero ≠ Spin.minus := by decide
@[simp] theorem spin_plus_ne_zero : Spin.plus ≠ Spin.zero := by decide
@[simp] theorem spin_plus_ne_minus : Spin.plus ≠ Spin.minus := by decide
@[simp] theorem spin_minus_ne_zero : Spin.minus ≠ Spin.zero := by decide
@[simp] theorem spin_minus_ne_plus : Spin.minus ≠ Spin.plus := by decide

theorem sum_spin {R : Type*} [AddCommMonoid R] (f : Spin → R) :
    (∑ h : Spin, f h) = f Spin.zero + f Spin.plus + f Spin.minus := by
  have hu : (Finset.univ : Finset Spin) = {Spin.zero,Spin.plus,Spin.minus} := by
    ext h; cases h <;> simp
  rw [hu]
  simp [add_assoc]

theorem sum_pair {R : Type*} [AddCommMonoid R] (f : Pair → R) :
    (∑ a : Pair, f a) =
      (f (.zero,.zero)+f (.zero,.plus)+f (.zero,.minus))+
      (f (.plus,.zero)+f (.plus,.plus)+f (.plus,.minus))+
      (f (.minus,.zero)+f (.minus,.plus)+f (.minus,.minus)) := by
  rw [Fintype.sum_prod_type]
  simp only [sum_spin]

@[simp] theorem cup_zero_zero : cup (.zero,.zero)=1 := by norm_num [cup,charge]
@[simp] theorem cup_plus_minus : cup (.plus,.minus)=q^5 := by norm_num [cup,charge]
@[simp] theorem cup_minus_plus : cup (.minus,.plus)= -q^3 := by
  norm_num [cup,charge,zpow_neg,q_five_inv]

theorem cup_norm : (∑ a : Pair, cup a * cup a) = -nZero := by
  rw [sum_pair]
  norm_num [cup,charge,zpow_neg,q_five_inv]
  rw [nZero,← q_two_sum]
  linear_combination q^2 * q_pow_eight

theorem cup_insertion_zero : (∑ a : Pair, cup a * insertion a Spin.zero) = 0 := by
  rw [sum_pair]
  norm_num [cup,insertion,charge,zpow_neg,q_five_inv,q_four_inv]
  have hx := xStar_mul_q_sum
  rw [q_inv] at hx
  linear_combination -hx + xStar*q*q_pow_eight

theorem cup_insertion (h : Spin) : (∑ a : Pair, cup a * insertion a h) = 0 := by
  cases h with
  | zero => exact cup_insertion_zero
  | plus => rw [sum_pair]; norm_num [cup,insertion,charge]
  | minus => rw [sum_pair]; norm_num [cup,insertion,charge]

theorem insertion_zero_norm : (∑ a : Pair, insertion a Spin.zero * insertion a Spin.zero) = nZero := by
  rw [sum_pair]
  norm_num [insertion,charge,zpow_neg,q_four_inv]
  linear_combination xStar_sq_twice + 2*xStar^2*q_pow_eight

theorem insertion_plus_norm : (∑ a : Pair, insertion a Spin.plus * insertion a Spin.plus) = nZero := by
  rw [sum_pair]
  norm_num [insertion,charge,zpow_neg,q_inv]
  have h := xStar_sq_mul_sqrt_two
  rw [← q_two_sum] at h
  linear_combination h + xStar^2*q^6*q_pow_eight

theorem insertion_minus_norm : (∑ a : Pair, insertion a Spin.minus * insertion a Spin.minus) = nZero := by
  rw [sum_pair]
  norm_num [insertion,charge,zpow_neg,q_inv]
  have h := xStar_sq_mul_sqrt_two
  rw [← q_two_sum] at h
  linear_combination h + xStar^2*q^6*q_pow_eight

theorem insertion_gram (h k : Spin) :
    (∑ a : Pair, insertion a h * insertion a k) = if h=k then nZero else 0 := by
  cases h <;> cases k
  · simpa using insertion_zero_norm
  · rw [sum_pair]; norm_num [insertion,charge]
  · rw [sum_pair]; norm_num [insertion,charge]
  · rw [sum_pair]; norm_num [insertion,charge]
  · simpa using insertion_plus_norm
  · rw [sum_pair]; norm_num [insertion,charge]
  · rw [sum_pair]; norm_num [insertion,charge]
  · rw [sum_pair]; norm_num [insertion,charge]
  · simpa using insertion_minus_norm

end PolynomialVacuumAlgebra

end OAI
