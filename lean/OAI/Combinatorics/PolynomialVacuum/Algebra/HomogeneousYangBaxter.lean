import OAI.Combinatorics.PolynomialVacuum.Algebra.Table

namespace OAI

namespace PolynomialVacuumAlgebra

 
noncomputable def hybLeft (x y z : ℂ) (a b c d e f : Spin) : ℂ :=
  ∑ i : Spin, ∑ j : Spin, ∑ k : Spin,
    exchangeNumerator x y (a,b) (i,j) *
    exchangeNumerator x z (j,c) (k,f) *
    exchangeNumerator y z (i,k) (d,e)

 
noncomputable def hybRight (x y z : ℂ) (a b c d e f : Spin) : ℂ :=
  ∑ i : Spin, ∑ j : Spin, ∑ k : Spin,
    exchangeNumerator y z (b,c) (j,k) *
    exchangeNumerator x z (a,j) (d,i) *
    exchangeNumerator x y (i,k) (e,f)

theorem hyb_entry_0_0 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .zero .zero .zero = hybRight x y z .zero .zero .zero .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_0_1 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .zero .zero .plus = hybRight x y z .zero .zero .zero .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_2 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .zero .zero .minus = hybRight x y z .zero .zero .zero .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_3 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .zero .plus .zero = hybRight x y z .zero .zero .zero .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_4 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .zero .plus .plus = hybRight x y z .zero .zero .zero .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_5 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .zero .plus .minus = hybRight x y z .zero .zero .zero .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_0_6 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .zero .minus .zero = hybRight x y z .zero .zero .zero .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_7 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .zero .minus .plus = hybRight x y z .zero .zero .zero .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_0_8 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .zero .minus .minus = hybRight x y z .zero .zero .zero .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_9 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .plus .zero .zero = hybRight x y z .zero .zero .zero .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_10 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .plus .zero .plus = hybRight x y z .zero .zero .zero .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_11 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .plus .zero .minus = hybRight x y z .zero .zero .zero .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_0_12 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .plus .plus .zero = hybRight x y z .zero .zero .zero .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_13 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .plus .plus .plus = hybRight x y z .zero .zero .zero .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_14 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .plus .plus .minus = hybRight x y z .zero .zero .zero .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_15 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .plus .minus .zero = hybRight x y z .zero .zero .zero .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_0_16 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .plus .minus .plus = hybRight x y z .zero .zero .zero .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_17 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .plus .minus .minus = hybRight x y z .zero .zero .zero .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_18 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .minus .zero .zero = hybRight x y z .zero .zero .zero .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_19 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .minus .zero .plus = hybRight x y z .zero .zero .zero .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_0_20 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .minus .zero .minus = hybRight x y z .zero .zero .zero .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_21 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .minus .plus .zero = hybRight x y z .zero .zero .zero .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_0_22 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .minus .plus .plus = hybRight x y z .zero .zero .zero .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_23 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .minus .plus .minus = hybRight x y z .zero .zero .zero .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_24 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .minus .minus .zero = hybRight x y z .zero .zero .zero .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_25 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .minus .minus .plus = hybRight x y z .zero .zero .zero .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_0_26 (x y z : ℂ) :
    hybLeft x y z .zero .zero .zero .minus .minus .minus = hybRight x y z .zero .zero .zero .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_0 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .zero .zero .zero = hybRight x y z .zero .zero .plus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_1 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .zero .zero .plus = hybRight x y z .zero .zero .plus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_1_2 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .zero .zero .minus = hybRight x y z .zero .zero .plus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_3 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .zero .plus .zero = hybRight x y z .zero .zero .plus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_1_4 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .zero .plus .plus = hybRight x y z .zero .zero .plus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_5 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .zero .plus .minus = hybRight x y z .zero .zero .plus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_6 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .zero .minus .zero = hybRight x y z .zero .zero .plus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_7 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .zero .minus .plus = hybRight x y z .zero .zero .plus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_8 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .zero .minus .minus = hybRight x y z .zero .zero .plus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_1_9 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .plus .zero .zero = hybRight x y z .zero .zero .plus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_1_10 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .plus .zero .plus = hybRight x y z .zero .zero .plus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_11 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .plus .zero .minus = hybRight x y z .zero .zero .plus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_12 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .plus .plus .zero = hybRight x y z .zero .zero .plus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_13 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .plus .plus .plus = hybRight x y z .zero .zero .plus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_14 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .plus .plus .minus = hybRight x y z .zero .zero .plus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_1_15 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .plus .minus .zero = hybRight x y z .zero .zero .plus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_16 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .plus .minus .plus = hybRight x y z .zero .zero .plus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_1_17 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .plus .minus .minus = hybRight x y z .zero .zero .plus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_18 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .minus .zero .zero = hybRight x y z .zero .zero .plus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_19 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .minus .zero .plus = hybRight x y z .zero .zero .plus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_20 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .minus .zero .minus = hybRight x y z .zero .zero .plus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_1_21 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .minus .plus .zero = hybRight x y z .zero .zero .plus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_22 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .minus .plus .plus = hybRight x y z .zero .zero .plus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_1_23 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .minus .plus .minus = hybRight x y z .zero .zero .plus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_24 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .minus .minus .zero = hybRight x y z .zero .zero .plus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_1_25 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .minus .minus .plus = hybRight x y z .zero .zero .plus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_1_26 (x y z : ℂ) :
    hybLeft x y z .zero .zero .plus .minus .minus .minus = hybRight x y z .zero .zero .plus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_2_0 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .zero .zero .zero = hybRight x y z .zero .zero .minus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_2_1 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .zero .zero .plus = hybRight x y z .zero .zero .minus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_2_2 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .zero .zero .minus = hybRight x y z .zero .zero .minus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_2_3 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .zero .plus .zero = hybRight x y z .zero .zero .minus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_2_4 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .zero .plus .plus = hybRight x y z .zero .zero .minus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_2_5 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .zero .plus .minus = hybRight x y z .zero .zero .minus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_2_6 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .zero .minus .zero = hybRight x y z .zero .zero .minus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_2_7 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .zero .minus .plus = hybRight x y z .zero .zero .minus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_2_8 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .zero .minus .minus = hybRight x y z .zero .zero .minus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_2_9 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .plus .zero .zero = hybRight x y z .zero .zero .minus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_2_10 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .plus .zero .plus = hybRight x y z .zero .zero .minus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_2_11 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .plus .zero .minus = hybRight x y z .zero .zero .minus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_2_12 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .plus .plus .zero = hybRight x y z .zero .zero .minus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_2_13 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .plus .plus .plus = hybRight x y z .zero .zero .minus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_2_14 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .plus .plus .minus = hybRight x y z .zero .zero .minus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_2_15 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .plus .minus .zero = hybRight x y z .zero .zero .minus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_2_16 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .plus .minus .plus = hybRight x y z .zero .zero .minus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_2_17 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .plus .minus .minus = hybRight x y z .zero .zero .minus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_2_18 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .minus .zero .zero = hybRight x y z .zero .zero .minus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_2_19 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .minus .zero .plus = hybRight x y z .zero .zero .minus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_2_20 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .minus .zero .minus = hybRight x y z .zero .zero .minus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_2_21 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .minus .plus .zero = hybRight x y z .zero .zero .minus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_2_22 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .minus .plus .plus = hybRight x y z .zero .zero .minus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_2_23 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .minus .plus .minus = hybRight x y z .zero .zero .minus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_2_24 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .minus .minus .zero = hybRight x y z .zero .zero .minus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_2_25 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .minus .minus .plus = hybRight x y z .zero .zero .minus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_2_26 (x y z : ℂ) :
    hybLeft x y z .zero .zero .minus .minus .minus .minus = hybRight x y z .zero .zero .minus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_0 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .zero .zero .zero = hybRight x y z .zero .plus .zero .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_1 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .zero .zero .plus = hybRight x y z .zero .plus .zero .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_3_2 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .zero .zero .minus = hybRight x y z .zero .plus .zero .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_3 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .zero .plus .zero = hybRight x y z .zero .plus .zero .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_3_4 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .zero .plus .plus = hybRight x y z .zero .plus .zero .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_5 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .zero .plus .minus = hybRight x y z .zero .plus .zero .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_6 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .zero .minus .zero = hybRight x y z .zero .plus .zero .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_7 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .zero .minus .plus = hybRight x y z .zero .plus .zero .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_8 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .zero .minus .minus = hybRight x y z .zero .plus .zero .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_3_9 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .plus .zero .zero = hybRight x y z .zero .plus .zero .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_3_10 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .plus .zero .plus = hybRight x y z .zero .plus .zero .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_11 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .plus .zero .minus = hybRight x y z .zero .plus .zero .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_12 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .plus .plus .zero = hybRight x y z .zero .plus .zero .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_13 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .plus .plus .plus = hybRight x y z .zero .plus .zero .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_14 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .plus .plus .minus = hybRight x y z .zero .plus .zero .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13]
  all_goals ring

theorem hyb_entry_3_15 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .plus .minus .zero = hybRight x y z .zero .plus .zero .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_16 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .plus .minus .plus = hybRight x y z .zero .plus .zero .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13]
  all_goals ring

theorem hyb_entry_3_17 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .plus .minus .minus = hybRight x y z .zero .plus .zero .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_18 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .minus .zero .zero = hybRight x y z .zero .plus .zero .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_19 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .minus .zero .plus = hybRight x y z .zero .plus .zero .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_20 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .minus .zero .minus = hybRight x y z .zero .plus .zero .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_3_21 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .minus .plus .zero = hybRight x y z .zero .plus .zero .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_22 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .minus .plus .plus = hybRight x y z .zero .plus .zero .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13]
  all_goals ring

theorem hyb_entry_3_23 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .minus .plus .minus = hybRight x y z .zero .plus .zero .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_24 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .minus .minus .zero = hybRight x y z .zero .plus .zero .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_25 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .minus .minus .plus = hybRight x y z .zero .plus .zero .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_3_26 (x y z : ℂ) :
    hybLeft x y z .zero .plus .zero .minus .minus .minus = hybRight x y z .zero .plus .zero .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_4_0 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .zero .zero .zero = hybRight x y z .zero .plus .plus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_1 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .zero .zero .plus = hybRight x y z .zero .plus .plus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_2 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .zero .zero .minus = hybRight x y z .zero .plus .plus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_3 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .zero .plus .zero = hybRight x y z .zero .plus .plus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_4 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .zero .plus .plus = hybRight x y z .zero .plus .plus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_4_5 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .zero .plus .minus = hybRight x y z .zero .plus .plus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_6 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .zero .minus .zero = hybRight x y z .zero .plus .plus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_4_7 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .zero .minus .plus = hybRight x y z .zero .plus .plus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_8 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .zero .minus .minus = hybRight x y z .zero .plus .plus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_4_9 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .plus .zero .zero = hybRight x y z .zero .plus .plus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_10 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .plus .zero .plus = hybRight x y z .zero .plus .plus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_4_11 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .plus .zero .minus = hybRight x y z .zero .plus .plus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_12 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .plus .plus .zero = hybRight x y z .zero .plus .plus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_4_13 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .plus .plus .plus = hybRight x y z .zero .plus .plus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_14 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .plus .plus .minus = hybRight x y z .zero .plus .plus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_15 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .plus .minus .zero = hybRight x y z .zero .plus .plus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_16 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .plus .minus .plus = hybRight x y z .zero .plus .plus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_17 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .plus .minus .minus = hybRight x y z .zero .plus .plus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_18 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .minus .zero .zero = hybRight x y z .zero .plus .plus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_19 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .minus .zero .plus = hybRight x y z .zero .plus .plus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_20 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .minus .zero .minus = hybRight x y z .zero .plus .plus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_4_21 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .minus .plus .zero = hybRight x y z .zero .plus .plus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_22 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .minus .plus .plus = hybRight x y z .zero .plus .plus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_23 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .minus .plus .minus = hybRight x y z .zero .plus .plus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_24 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .minus .minus .zero = hybRight x y z .zero .plus .plus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_4_25 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .minus .minus .plus = hybRight x y z .zero .plus .plus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_4_26 (x y z : ℂ) :
    hybLeft x y z .zero .plus .plus .minus .minus .minus = hybRight x y z .zero .plus .plus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_5_0 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .zero .zero .zero = hybRight x y z .zero .plus .minus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_5_1 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .zero .zero .plus = hybRight x y z .zero .plus .minus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_5_2 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .zero .zero .minus = hybRight x y z .zero .plus .minus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_5_3 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .zero .plus .zero = hybRight x y z .zero .plus .minus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_5_4 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .zero .plus .plus = hybRight x y z .zero .plus .minus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_5_5 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .zero .plus .minus = hybRight x y z .zero .plus .minus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_5_6 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .zero .minus .zero = hybRight x y z .zero .plus .minus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_5_7 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .zero .minus .plus = hybRight x y z .zero .plus .minus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_5_8 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .zero .minus .minus = hybRight x y z .zero .plus .minus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_5_9 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .plus .zero .zero = hybRight x y z .zero .plus .minus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_5_10 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .plus .zero .plus = hybRight x y z .zero .plus .minus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_5_11 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .plus .zero .minus = hybRight x y z .zero .plus .minus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_5_12 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .plus .plus .zero = hybRight x y z .zero .plus .minus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_5_13 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .plus .plus .plus = hybRight x y z .zero .plus .minus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_5_14 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .plus .plus .minus = hybRight x y z .zero .plus .minus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_5_15 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .plus .minus .zero = hybRight x y z .zero .plus .minus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_5_16 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .plus .minus .plus = hybRight x y z .zero .plus .minus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_5_17 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .plus .minus .minus = hybRight x y z .zero .plus .minus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_5_18 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .minus .zero .zero = hybRight x y z .zero .plus .minus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_5_19 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .minus .zero .plus = hybRight x y z .zero .plus .minus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_5_20 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .minus .zero .minus = hybRight x y z .zero .plus .minus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_5_21 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .minus .plus .zero = hybRight x y z .zero .plus .minus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_5_22 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .minus .plus .plus = hybRight x y z .zero .plus .minus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_5_23 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .minus .plus .minus = hybRight x y z .zero .plus .minus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_5_24 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .minus .minus .zero = hybRight x y z .zero .plus .minus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_5_25 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .minus .minus .plus = hybRight x y z .zero .plus .minus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_5_26 (x y z : ℂ) :
    hybLeft x y z .zero .plus .minus .minus .minus .minus = hybRight x y z .zero .plus .minus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_0 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .zero .zero .zero = hybRight x y z .zero .minus .zero .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_1 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .zero .zero .plus = hybRight x y z .zero .minus .zero .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_2 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .zero .zero .minus = hybRight x y z .zero .minus .zero .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_6_3 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .zero .plus .zero = hybRight x y z .zero .minus .zero .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_4 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .zero .plus .plus = hybRight x y z .zero .minus .zero .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_6_5 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .zero .plus .minus = hybRight x y z .zero .minus .zero .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_6 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .zero .minus .zero = hybRight x y z .zero .minus .zero .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_6_7 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .zero .minus .plus = hybRight x y z .zero .minus .zero .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_8 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .zero .minus .minus = hybRight x y z .zero .minus .zero .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_9 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .plus .zero .zero = hybRight x y z .zero .minus .zero .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_10 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .plus .zero .plus = hybRight x y z .zero .minus .zero .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_6_11 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .plus .zero .minus = hybRight x y z .zero .minus .zero .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_12 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .plus .plus .zero = hybRight x y z .zero .minus .zero .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_13 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .plus .plus .plus = hybRight x y z .zero .minus .zero .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_6_14 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .plus .plus .minus = hybRight x y z .zero .minus .zero .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_15 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .plus .minus .zero = hybRight x y z .zero .minus .zero .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_16 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .plus .minus .plus = hybRight x y z .zero .minus .zero .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_17 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .plus .minus .minus = hybRight x y z .zero .minus .zero .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13]
  all_goals ring

theorem hyb_entry_6_18 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .minus .zero .zero = hybRight x y z .zero .minus .zero .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_6_19 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .minus .zero .plus = hybRight x y z .zero .minus .zero .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_20 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .minus .zero .minus = hybRight x y z .zero .minus .zero .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_21 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .minus .plus .zero = hybRight x y z .zero .minus .zero .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_22 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .minus .plus .plus = hybRight x y z .zero .minus .zero .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_23 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .minus .plus .minus = hybRight x y z .zero .minus .zero .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13]
  all_goals ring

theorem hyb_entry_6_24 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .minus .minus .zero = hybRight x y z .zero .minus .zero .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_6_25 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .minus .minus .plus = hybRight x y z .zero .minus .zero .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13]
  all_goals ring

theorem hyb_entry_6_26 (x y z : ℂ) :
    hybLeft x y z .zero .minus .zero .minus .minus .minus = hybRight x y z .zero .minus .zero .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_0 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .zero .zero .zero = hybRight x y z .zero .minus .plus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_7_1 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .zero .zero .plus = hybRight x y z .zero .minus .plus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_2 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .zero .zero .minus = hybRight x y z .zero .minus .plus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_3 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .zero .plus .zero = hybRight x y z .zero .minus .plus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_4 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .zero .plus .plus = hybRight x y z .zero .minus .plus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_5 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .zero .plus .minus = hybRight x y z .zero .minus .plus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_7_6 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .zero .minus .zero = hybRight x y z .zero .minus .plus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_7 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .zero .minus .plus = hybRight x y z .zero .minus .plus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_7_8 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .zero .minus .minus = hybRight x y z .zero .minus .plus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_9 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .plus .zero .zero = hybRight x y z .zero .minus .plus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_10 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .plus .zero .plus = hybRight x y z .zero .minus .plus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_7_11 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .plus .zero .minus = hybRight x y z .zero .minus .plus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_7_12 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .plus .plus .zero = hybRight x y z .zero .minus .plus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_13 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .plus .plus .plus = hybRight x y z .zero .minus .plus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_14 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .plus .plus .minus = hybRight x y z .zero .minus .plus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_15 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .plus .minus .zero = hybRight x y z .zero .minus .plus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_7_16 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .plus .minus .plus = hybRight x y z .zero .minus .plus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_17 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .plus .minus .minus = hybRight x y z .zero .minus .plus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_18 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .minus .zero .zero = hybRight x y z .zero .minus .plus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_19 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .minus .zero .plus = hybRight x y z .zero .minus .plus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_7_20 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .minus .zero .minus = hybRight x y z .zero .minus .plus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_7_21 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .minus .plus .zero = hybRight x y z .zero .minus .plus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_7_22 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .minus .plus .plus = hybRight x y z .zero .minus .plus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_23 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .minus .plus .minus = hybRight x y z .zero .minus .plus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_24 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .minus .minus .zero = hybRight x y z .zero .minus .plus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_7_25 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .minus .minus .plus = hybRight x y z .zero .minus .plus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_7_26 (x y z : ℂ) :
    hybLeft x y z .zero .minus .plus .minus .minus .minus = hybRight x y z .zero .minus .plus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_0 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .zero .zero .zero = hybRight x y z .zero .minus .minus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_1 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .zero .zero .plus = hybRight x y z .zero .minus .minus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_2 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .zero .zero .minus = hybRight x y z .zero .minus .minus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_3 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .zero .plus .zero = hybRight x y z .zero .minus .minus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_8_4 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .zero .plus .plus = hybRight x y z .zero .minus .minus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_8_5 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .zero .plus .minus = hybRight x y z .zero .minus .minus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_6 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .zero .minus .zero = hybRight x y z .zero .minus .minus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_7 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .zero .minus .plus = hybRight x y z .zero .minus .minus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_8 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .zero .minus .minus = hybRight x y z .zero .minus .minus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_8_9 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .plus .zero .zero = hybRight x y z .zero .minus .minus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_10 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .plus .zero .plus = hybRight x y z .zero .minus .minus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_8_11 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .plus .zero .minus = hybRight x y z .zero .minus .minus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_12 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .plus .plus .zero = hybRight x y z .zero .minus .minus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_8_13 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .plus .plus .plus = hybRight x y z .zero .minus .minus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_8_14 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .plus .plus .minus = hybRight x y z .zero .minus .minus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_15 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .plus .minus .zero = hybRight x y z .zero .minus .minus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_16 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .plus .minus .plus = hybRight x y z .zero .minus .minus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_17 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .plus .minus .minus = hybRight x y z .zero .minus .minus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_18 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .minus .zero .zero = hybRight x y z .zero .minus .minus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_19 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .minus .zero .plus = hybRight x y z .zero .minus .minus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_20 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .minus .zero .minus = hybRight x y z .zero .minus .minus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_8_21 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .minus .plus .zero = hybRight x y z .zero .minus .minus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_22 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .minus .plus .plus = hybRight x y z .zero .minus .minus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_23 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .minus .plus .minus = hybRight x y z .zero .minus .minus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_24 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .minus .minus .zero = hybRight x y z .zero .minus .minus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_8_25 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .minus .minus .plus = hybRight x y z .zero .minus .minus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_8_26 (x y z : ℂ) :
    hybLeft x y z .zero .minus .minus .minus .minus .minus = hybRight x y z .zero .minus .minus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_0 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .zero .zero .zero = hybRight x y z .plus .zero .zero .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_1 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .zero .zero .plus = hybRight x y z .plus .zero .zero .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_9_2 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .zero .zero .minus = hybRight x y z .plus .zero .zero .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_3 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .zero .plus .zero = hybRight x y z .plus .zero .zero .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_9_4 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .zero .plus .plus = hybRight x y z .plus .zero .zero .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_5 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .zero .plus .minus = hybRight x y z .plus .zero .zero .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_6 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .zero .minus .zero = hybRight x y z .plus .zero .zero .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_9_7 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .zero .minus .plus = hybRight x y z .plus .zero .zero .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_8 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .zero .minus .minus = hybRight x y z .plus .zero .zero .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_9 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .plus .zero .zero = hybRight x y z .plus .zero .zero .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_9_10 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .plus .zero .plus = hybRight x y z .plus .zero .zero .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_11 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .plus .zero .minus = hybRight x y z .plus .zero .zero .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_12 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .plus .plus .zero = hybRight x y z .plus .zero .zero .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_13 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .plus .plus .plus = hybRight x y z .plus .zero .zero .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_14 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .plus .plus .minus = hybRight x y z .plus .zero .zero .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_9_15 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .plus .minus .zero = hybRight x y z .plus .zero .zero .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_16 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .plus .minus .plus = hybRight x y z .plus .zero .zero .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_9_17 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .plus .minus .minus = hybRight x y z .plus .zero .zero .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_18 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .minus .zero .zero = hybRight x y z .plus .zero .zero .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_19 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .minus .zero .plus = hybRight x y z .plus .zero .zero .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_20 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .minus .zero .minus = hybRight x y z .plus .zero .zero .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_9_21 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .minus .plus .zero = hybRight x y z .plus .zero .zero .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_22 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .minus .plus .plus = hybRight x y z .plus .zero .zero .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_9_23 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .minus .plus .minus = hybRight x y z .plus .zero .zero .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_24 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .minus .minus .zero = hybRight x y z .plus .zero .zero .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_25 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .minus .minus .plus = hybRight x y z .plus .zero .zero .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_9_26 (x y z : ℂ) :
    hybLeft x y z .plus .zero .zero .minus .minus .minus = hybRight x y z .plus .zero .zero .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_0 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .zero .zero .zero = hybRight x y z .plus .zero .plus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_1 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .zero .zero .plus = hybRight x y z .plus .zero .plus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_2 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .zero .zero .minus = hybRight x y z .plus .zero .plus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_3 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .zero .plus .zero = hybRight x y z .plus .zero .plus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_4 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .zero .plus .plus = hybRight x y z .plus .zero .plus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_10_5 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .zero .plus .minus = hybRight x y z .plus .zero .plus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_6 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .zero .minus .zero = hybRight x y z .plus .zero .plus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_10_7 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .zero .minus .plus = hybRight x y z .plus .zero .plus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_8 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .zero .minus .minus = hybRight x y z .plus .zero .plus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_10_9 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .plus .zero .zero = hybRight x y z .plus .zero .plus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_10 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .plus .zero .plus = hybRight x y z .plus .zero .plus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_10_11 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .plus .zero .minus = hybRight x y z .plus .zero .plus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_12 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .plus .plus .zero = hybRight x y z .plus .zero .plus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_10_13 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .plus .plus .plus = hybRight x y z .plus .zero .plus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_14 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .plus .plus .minus = hybRight x y z .plus .zero .plus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_15 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .plus .minus .zero = hybRight x y z .plus .zero .plus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_16 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .plus .minus .plus = hybRight x y z .plus .zero .plus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_17 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .plus .minus .minus = hybRight x y z .plus .zero .plus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_18 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .minus .zero .zero = hybRight x y z .plus .zero .plus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_10_19 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .minus .zero .plus = hybRight x y z .plus .zero .plus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_10_20 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .minus .zero .minus = hybRight x y z .plus .zero .plus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_10_21 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .minus .plus .zero = hybRight x y z .plus .zero .plus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_22 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .minus .plus .plus = hybRight x y z .plus .zero .plus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_23 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .minus .plus .minus = hybRight x y z .plus .zero .plus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_24 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .minus .minus .zero = hybRight x y z .plus .zero .plus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_10_25 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .minus .minus .plus = hybRight x y z .plus .zero .plus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_10_26 (x y z : ℂ) :
    hybLeft x y z .plus .zero .plus .minus .minus .minus = hybRight x y z .plus .zero .plus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_11_0 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .zero .zero .zero = hybRight x y z .plus .zero .minus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_11_1 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .zero .zero .plus = hybRight x y z .plus .zero .minus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_2 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .zero .zero .minus = hybRight x y z .plus .zero .minus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_3 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .zero .plus .zero = hybRight x y z .plus .zero .minus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_4 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .zero .plus .plus = hybRight x y z .plus .zero .minus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_11_5 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .zero .plus .minus = hybRight x y z .plus .zero .minus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_11_6 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .zero .minus .zero = hybRight x y z .plus .zero .minus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_7 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .zero .minus .plus = hybRight x y z .plus .zero .minus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_11_8 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .zero .minus .minus = hybRight x y z .plus .zero .minus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_9 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .plus .zero .zero = hybRight x y z .plus .zero .minus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_10 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .plus .zero .plus = hybRight x y z .plus .zero .minus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_11 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .plus .zero .minus = hybRight x y z .plus .zero .minus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_11_12 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .plus .plus .zero = hybRight x y z .plus .zero .minus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_13 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .plus .plus .plus = hybRight x y z .plus .zero .minus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_11_14 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .plus .plus .minus = hybRight x y z .plus .zero .minus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_15 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .plus .minus .zero = hybRight x y z .plus .zero .minus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_11_16 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .plus .minus .plus = hybRight x y z .plus .zero .minus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_17 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .plus .minus .minus = hybRight x y z .plus .zero .minus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_18 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .minus .zero .zero = hybRight x y z .plus .zero .minus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_19 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .minus .zero .plus = hybRight x y z .plus .zero .minus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_11_20 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .minus .zero .minus = hybRight x y z .plus .zero .minus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_21 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .minus .plus .zero = hybRight x y z .plus .zero .minus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_11_22 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .minus .plus .plus = hybRight x y z .plus .zero .minus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_23 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .minus .plus .minus = hybRight x y z .plus .zero .minus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_24 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .minus .minus .zero = hybRight x y z .plus .zero .minus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_25 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .minus .minus .plus = hybRight x y z .plus .zero .minus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_11_26 (x y z : ℂ) :
    hybLeft x y z .plus .zero .minus .minus .minus .minus = hybRight x y z .plus .zero .minus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_0 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .zero .zero .zero = hybRight x y z .plus .plus .zero .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_1 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .zero .zero .plus = hybRight x y z .plus .plus .zero .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_2 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .zero .zero .minus = hybRight x y z .plus .plus .zero .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_12_3 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .zero .plus .zero = hybRight x y z .plus .plus .zero .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_4 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .zero .plus .plus = hybRight x y z .plus .plus .zero .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_12_5 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .zero .plus .minus = hybRight x y z .plus .plus .zero .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_6 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .zero .minus .zero = hybRight x y z .plus .plus .zero .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_12_7 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .zero .minus .plus = hybRight x y z .plus .plus .zero .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_8 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .zero .minus .minus = hybRight x y z .plus .plus .zero .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_12_9 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .plus .zero .zero = hybRight x y z .plus .plus .zero .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_10 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .plus .zero .plus = hybRight x y z .plus .plus .zero .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_12_11 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .plus .zero .minus = hybRight x y z .plus .plus .zero .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_12 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .plus .plus .zero = hybRight x y z .plus .plus .zero .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_12_13 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .plus .plus .plus = hybRight x y z .plus .plus .zero .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_14 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .plus .plus .minus = hybRight x y z .plus .plus .zero .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_15 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .plus .minus .zero = hybRight x y z .plus .plus .zero .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_16 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .plus .minus .plus = hybRight x y z .plus .plus .zero .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_17 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .plus .minus .minus = hybRight x y z .plus .plus .zero .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_12_18 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .minus .zero .zero = hybRight x y z .plus .plus .zero .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_12_19 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .minus .zero .plus = hybRight x y z .plus .plus .zero .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_20 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .minus .zero .minus = hybRight x y z .plus .plus .zero .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_12_21 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .minus .plus .zero = hybRight x y z .plus .plus .zero .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_22 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .minus .plus .plus = hybRight x y z .plus .plus .zero .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_23 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .minus .plus .minus = hybRight x y z .plus .plus .zero .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_12_24 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .minus .minus .zero = hybRight x y z .plus .plus .zero .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_25 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .minus .minus .plus = hybRight x y z .plus .plus .zero .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_12_26 (x y z : ℂ) :
    hybLeft x y z .plus .plus .zero .minus .minus .minus = hybRight x y z .plus .plus .zero .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_13_0 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .zero .zero .zero = hybRight x y z .plus .plus .plus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_1 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .zero .zero .plus = hybRight x y z .plus .plus .plus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_2 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .zero .zero .minus = hybRight x y z .plus .plus .plus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_3 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .zero .plus .zero = hybRight x y z .plus .plus .plus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_4 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .zero .plus .plus = hybRight x y z .plus .plus .plus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_5 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .zero .plus .minus = hybRight x y z .plus .plus .plus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_6 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .zero .minus .zero = hybRight x y z .plus .plus .plus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_13_7 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .zero .minus .plus = hybRight x y z .plus .plus .plus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_8 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .zero .minus .minus = hybRight x y z .plus .plus .plus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_13_9 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .plus .zero .zero = hybRight x y z .plus .plus .plus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_10 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .plus .zero .plus = hybRight x y z .plus .plus .plus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_11 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .plus .zero .minus = hybRight x y z .plus .plus .plus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_12 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .plus .plus .zero = hybRight x y z .plus .plus .plus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_13 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .plus .plus .plus = hybRight x y z .plus .plus .plus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_13_14 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .plus .plus .minus = hybRight x y z .plus .plus .plus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_15 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .plus .minus .zero = hybRight x y z .plus .plus .plus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_13_16 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .plus .minus .plus = hybRight x y z .plus .plus .plus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_17 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .plus .minus .minus = hybRight x y z .plus .plus .plus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_18 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .minus .zero .zero = hybRight x y z .plus .plus .plus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_19 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .minus .zero .plus = hybRight x y z .plus .plus .plus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_20 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .minus .zero .minus = hybRight x y z .plus .plus .plus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_13_21 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .minus .plus .zero = hybRight x y z .plus .plus .plus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_22 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .minus .plus .plus = hybRight x y z .plus .plus .plus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_23 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .minus .plus .minus = hybRight x y z .plus .plus .plus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_24 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .minus .minus .zero = hybRight x y z .plus .plus .plus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_13_25 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .minus .minus .plus = hybRight x y z .plus .plus .plus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_13_26 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .minus .minus .minus = hybRight x y z .plus .plus .plus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_14_0 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .zero .zero .zero = hybRight x y z .plus .plus .minus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_1 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .zero .zero .plus = hybRight x y z .plus .plus .minus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_14_2 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .zero .zero .minus = hybRight x y z .plus .plus .minus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_3 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .zero .plus .zero = hybRight x y z .plus .plus .minus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13]
  all_goals ring

theorem hyb_entry_14_4 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .zero .plus .plus = hybRight x y z .plus .plus .minus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_5 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .zero .plus .minus = hybRight x y z .plus .plus .minus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_6 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .zero .minus .zero = hybRight x y z .plus .plus .minus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_7 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .zero .minus .plus = hybRight x y z .plus .plus .minus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_8 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .zero .minus .minus = hybRight x y z .plus .plus .minus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_9 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .plus .zero .zero = hybRight x y z .plus .plus .minus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_14_10 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .plus .zero .plus = hybRight x y z .plus .plus .minus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_11 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .plus .zero .minus = hybRight x y z .plus .plus .minus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_12 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .plus .plus .zero = hybRight x y z .plus .plus .minus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_13 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .plus .plus .plus = hybRight x y z .plus .plus .minus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_14 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .plus .plus .minus = hybRight x y z .plus .plus .minus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_14_15 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .plus .minus .zero = hybRight x y z .plus .plus .minus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_16 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .plus .minus .plus = hybRight x y z .plus .plus .minus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_14_17 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .plus .minus .minus = hybRight x y z .plus .plus .minus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_18 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .minus .zero .zero = hybRight x y z .plus .plus .minus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_19 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .minus .zero .plus = hybRight x y z .plus .plus .minus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_20 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .minus .zero .minus = hybRight x y z .plus .plus .minus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_14_21 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .minus .plus .zero = hybRight x y z .plus .plus .minus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_22 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .minus .plus .plus = hybRight x y z .plus .plus .minus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_14_23 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .minus .plus .minus = hybRight x y z .plus .plus .minus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_24 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .minus .minus .zero = hybRight x y z .plus .plus .minus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_25 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .minus .minus .plus = hybRight x y z .plus .plus .minus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_14_26 (x y z : ℂ) :
    hybLeft x y z .plus .plus .minus .minus .minus .minus = hybRight x y z .plus .plus .minus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_0 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .zero .zero .zero = hybRight x y z .plus .minus .zero .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_15_1 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .zero .zero .plus = hybRight x y z .plus .minus .zero .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_2 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .zero .zero .minus = hybRight x y z .plus .minus .zero .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_3 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .zero .plus .zero = hybRight x y z .plus .minus .zero .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_4 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .zero .plus .plus = hybRight x y z .plus .minus .zero .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_5 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .zero .plus .minus = hybRight x y z .plus .minus .zero .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_15_6 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .zero .minus .zero = hybRight x y z .plus .minus .zero .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_7 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .zero .minus .plus = hybRight x y z .plus .minus .zero .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_15_8 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .zero .minus .minus = hybRight x y z .plus .minus .zero .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_9 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .plus .zero .zero = hybRight x y z .plus .minus .zero .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_10 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .plus .zero .plus = hybRight x y z .plus .minus .zero .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_11 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .plus .zero .minus = hybRight x y z .plus .minus .zero .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_15_12 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .plus .plus .zero = hybRight x y z .plus .minus .zero .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_13 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .plus .plus .plus = hybRight x y z .plus .minus .zero .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_15_14 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .plus .plus .minus = hybRight x y z .plus .minus .zero .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_15 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .plus .minus .zero = hybRight x y z .plus .minus .zero .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_15_16 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .plus .minus .plus = hybRight x y z .plus .minus .zero .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_17 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .plus .minus .minus = hybRight x y z .plus .minus .zero .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_18 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .minus .zero .zero = hybRight x y z .plus .minus .zero .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_19 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .minus .zero .plus = hybRight x y z .plus .minus .zero .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_15_20 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .minus .zero .minus = hybRight x y z .plus .minus .zero .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_21 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .minus .plus .zero = hybRight x y z .plus .minus .zero .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_15_22 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .minus .plus .plus = hybRight x y z .plus .minus .zero .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_23 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .minus .plus .minus = hybRight x y z .plus .minus .zero .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_24 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .minus .minus .zero = hybRight x y z .plus .minus .zero .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_25 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .minus .minus .plus = hybRight x y z .plus .minus .zero .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_15_26 (x y z : ℂ) :
    hybLeft x y z .plus .minus .zero .minus .minus .minus = hybRight x y z .plus .minus .zero .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_0 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .zero .zero .zero = hybRight x y z .plus .minus .plus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_1 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .zero .zero .plus = hybRight x y z .plus .minus .plus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_16_2 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .zero .zero .minus = hybRight x y z .plus .minus .plus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_3 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .zero .plus .zero = hybRight x y z .plus .minus .plus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13]
  all_goals ring

theorem hyb_entry_16_4 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .zero .plus .plus = hybRight x y z .plus .minus .plus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_5 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .zero .plus .minus = hybRight x y z .plus .minus .plus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_6 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .zero .minus .zero = hybRight x y z .plus .minus .plus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_7 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .zero .minus .plus = hybRight x y z .plus .minus .plus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_8 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .zero .minus .minus = hybRight x y z .plus .minus .plus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_9 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .plus .zero .zero = hybRight x y z .plus .minus .plus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_16_10 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .plus .zero .plus = hybRight x y z .plus .minus .plus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_11 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .plus .zero .minus = hybRight x y z .plus .minus .plus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_12 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .plus .plus .zero = hybRight x y z .plus .minus .plus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_13 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .plus .plus .plus = hybRight x y z .plus .minus .plus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_14 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .plus .plus .minus = hybRight x y z .plus .minus .plus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_16_15 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .plus .minus .zero = hybRight x y z .plus .minus .plus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_16 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .plus .minus .plus = hybRight x y z .plus .minus .plus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_16_17 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .plus .minus .minus = hybRight x y z .plus .minus .plus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_18 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .minus .zero .zero = hybRight x y z .plus .minus .plus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_19 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .minus .zero .plus = hybRight x y z .plus .minus .plus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_20 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .minus .zero .minus = hybRight x y z .plus .minus .plus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_16_21 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .minus .plus .zero = hybRight x y z .plus .minus .plus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_22 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .minus .plus .plus = hybRight x y z .plus .minus .plus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_16_23 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .minus .plus .minus = hybRight x y z .plus .minus .plus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_24 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .minus .minus .zero = hybRight x y z .plus .minus .plus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_16_25 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .minus .minus .plus = hybRight x y z .plus .minus .plus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_16_26 (x y z : ℂ) :
    hybLeft x y z .plus .minus .plus .minus .minus .minus = hybRight x y z .plus .minus .plus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_0 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .zero .zero .zero = hybRight x y z .plus .minus .minus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_1 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .zero .zero .plus = hybRight x y z .plus .minus .minus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_2 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .zero .zero .minus = hybRight x y z .plus .minus .minus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_17_3 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .zero .plus .zero = hybRight x y z .plus .minus .minus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_4 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .zero .plus .plus = hybRight x y z .plus .minus .minus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_17_5 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .zero .plus .minus = hybRight x y z .plus .minus .minus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_6 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .zero .minus .zero = hybRight x y z .plus .minus .minus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13]
  all_goals ring

theorem hyb_entry_17_7 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .zero .minus .plus = hybRight x y z .plus .minus .minus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_8 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .zero .minus .minus = hybRight x y z .plus .minus .minus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_9 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .plus .zero .zero = hybRight x y z .plus .minus .minus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_10 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .plus .zero .plus = hybRight x y z .plus .minus .minus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_17_11 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .plus .zero .minus = hybRight x y z .plus .minus .minus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_12 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .plus .plus .zero = hybRight x y z .plus .minus .minus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_17_13 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .plus .plus .plus = hybRight x y z .plus .minus .minus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_17_14 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .plus .plus .minus = hybRight x y z .plus .minus .minus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_15 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .plus .minus .zero = hybRight x y z .plus .minus .minus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_16 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .plus .minus .plus = hybRight x y z .plus .minus .minus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_17 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .plus .minus .minus = hybRight x y z .plus .minus .minus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_17_18 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .minus .zero .zero = hybRight x y z .plus .minus .minus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_17_19 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .minus .zero .plus = hybRight x y z .plus .minus .minus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_20 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .minus .zero .minus = hybRight x y z .plus .minus .minus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_21 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .minus .plus .zero = hybRight x y z .plus .minus .minus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_22 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .minus .plus .plus = hybRight x y z .plus .minus .minus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_23 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .minus .plus .minus = hybRight x y z .plus .minus .minus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_17_24 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .minus .minus .zero = hybRight x y z .plus .minus .minus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_17_25 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .minus .minus .plus = hybRight x y z .plus .minus .minus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_17_26 (x y z : ℂ) :
    hybLeft x y z .plus .minus .minus .minus .minus .minus = hybRight x y z .plus .minus .minus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_0 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .zero .zero .zero = hybRight x y z .minus .zero .zero .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_1 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .zero .zero .plus = hybRight x y z .minus .zero .zero .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_2 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .zero .zero .minus = hybRight x y z .minus .zero .zero .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_18_3 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .zero .plus .zero = hybRight x y z .minus .zero .zero .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_18_4 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .zero .plus .plus = hybRight x y z .minus .zero .zero .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_5 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .zero .plus .minus = hybRight x y z .minus .zero .zero .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_6 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .zero .minus .zero = hybRight x y z .minus .zero .zero .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_18_7 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .zero .minus .plus = hybRight x y z .minus .zero .zero .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_8 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .zero .minus .minus = hybRight x y z .minus .zero .zero .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_9 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .plus .zero .zero = hybRight x y z .minus .zero .zero .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_10 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .plus .zero .plus = hybRight x y z .minus .zero .zero .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_18_11 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .plus .zero .minus = hybRight x y z .minus .zero .zero .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_12 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .plus .plus .zero = hybRight x y z .minus .zero .zero .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_13 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .plus .plus .plus = hybRight x y z .minus .zero .zero .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_14 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .plus .plus .minus = hybRight x y z .minus .zero .zero .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_15 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .plus .minus .zero = hybRight x y z .minus .zero .zero .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_16 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .plus .minus .plus = hybRight x y z .minus .zero .zero .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_17 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .plus .minus .minus = hybRight x y z .minus .zero .zero .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_18_18 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .minus .zero .zero = hybRight x y z .minus .zero .zero .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_18_19 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .minus .zero .plus = hybRight x y z .minus .zero .zero .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_20 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .minus .zero .minus = hybRight x y z .minus .zero .zero .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_21 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .minus .plus .zero = hybRight x y z .minus .zero .zero .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_22 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .minus .plus .plus = hybRight x y z .minus .zero .zero .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_23 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .minus .plus .minus = hybRight x y z .minus .zero .zero .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_18_24 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .minus .minus .zero = hybRight x y z .minus .zero .zero .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_18_25 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .minus .minus .plus = hybRight x y z .minus .zero .zero .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_18_26 (x y z : ℂ) :
    hybLeft x y z .minus .zero .zero .minus .minus .minus = hybRight x y z .minus .zero .zero .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_0 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .zero .zero .zero = hybRight x y z .minus .zero .plus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_19_1 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .zero .zero .plus = hybRight x y z .minus .zero .plus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_2 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .zero .zero .minus = hybRight x y z .minus .zero .plus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_3 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .zero .plus .zero = hybRight x y z .minus .zero .plus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_4 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .zero .plus .plus = hybRight x y z .minus .zero .plus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_5 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .zero .plus .minus = hybRight x y z .minus .zero .plus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_19_6 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .zero .minus .zero = hybRight x y z .minus .zero .plus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_7 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .zero .minus .plus = hybRight x y z .minus .zero .plus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_19_8 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .zero .minus .minus = hybRight x y z .minus .zero .plus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_19_9 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .plus .zero .zero = hybRight x y z .minus .zero .plus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_10 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .plus .zero .plus = hybRight x y z .minus .zero .plus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_11 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .plus .zero .minus = hybRight x y z .minus .zero .plus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_19_12 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .plus .plus .zero = hybRight x y z .minus .zero .plus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_13 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .plus .plus .plus = hybRight x y z .minus .zero .plus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_14 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .plus .plus .minus = hybRight x y z .minus .zero .plus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_15 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .plus .minus .zero = hybRight x y z .minus .zero .plus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_19_16 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .plus .minus .plus = hybRight x y z .minus .zero .plus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_17 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .plus .minus .minus = hybRight x y z .minus .zero .plus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_18 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .minus .zero .zero = hybRight x y z .minus .zero .plus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_19 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .minus .zero .plus = hybRight x y z .minus .zero .plus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_19_20 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .minus .zero .minus = hybRight x y z .minus .zero .plus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_21 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .minus .plus .zero = hybRight x y z .minus .zero .plus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_19_22 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .minus .plus .plus = hybRight x y z .minus .zero .plus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_23 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .minus .plus .minus = hybRight x y z .minus .zero .plus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_24 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .minus .minus .zero = hybRight x y z .minus .zero .plus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_25 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .minus .minus .plus = hybRight x y z .minus .zero .plus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_19_26 (x y z : ℂ) :
    hybLeft x y z .minus .zero .plus .minus .minus .minus = hybRight x y z .minus .zero .plus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_20_0 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .zero .zero .zero = hybRight x y z .minus .zero .minus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_20_1 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .zero .zero .plus = hybRight x y z .minus .zero .minus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_20_2 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .zero .zero .minus = hybRight x y z .minus .zero .minus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_20_3 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .zero .plus .zero = hybRight x y z .minus .zero .minus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_20_4 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .zero .plus .plus = hybRight x y z .minus .zero .minus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_20_5 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .zero .plus .minus = hybRight x y z .minus .zero .minus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_20_6 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .zero .minus .zero = hybRight x y z .minus .zero .minus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_20_7 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .zero .minus .plus = hybRight x y z .minus .zero .minus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_20_8 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .zero .minus .minus = hybRight x y z .minus .zero .minus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_20_9 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .plus .zero .zero = hybRight x y z .minus .zero .minus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_20_10 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .plus .zero .plus = hybRight x y z .minus .zero .minus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_20_11 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .plus .zero .minus = hybRight x y z .minus .zero .minus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_20_12 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .plus .plus .zero = hybRight x y z .minus .zero .minus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_20_13 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .plus .plus .plus = hybRight x y z .minus .zero .minus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_20_14 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .plus .plus .minus = hybRight x y z .minus .zero .minus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_20_15 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .plus .minus .zero = hybRight x y z .minus .zero .minus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_20_16 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .plus .minus .plus = hybRight x y z .minus .zero .minus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_20_17 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .plus .minus .minus = hybRight x y z .minus .zero .minus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_20_18 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .minus .zero .zero = hybRight x y z .minus .zero .minus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_20_19 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .minus .zero .plus = hybRight x y z .minus .zero .minus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_20_20 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .minus .zero .minus = hybRight x y z .minus .zero .minus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_20_21 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .minus .plus .zero = hybRight x y z .minus .zero .minus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_20_22 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .minus .plus .plus = hybRight x y z .minus .zero .minus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_20_23 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .minus .plus .minus = hybRight x y z .minus .zero .minus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_20_24 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .minus .minus .zero = hybRight x y z .minus .zero .minus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_20_25 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .minus .minus .plus = hybRight x y z .minus .zero .minus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_20_26 (x y z : ℂ) :
    hybLeft x y z .minus .zero .minus .minus .minus .minus = hybRight x y z .minus .zero .minus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_0 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .zero .zero .zero = hybRight x y z .minus .plus .zero .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_21_1 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .zero .zero .plus = hybRight x y z .minus .plus .zero .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_2 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .zero .zero .minus = hybRight x y z .minus .plus .zero .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_3 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .zero .plus .zero = hybRight x y z .minus .plus .zero .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_4 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .zero .plus .plus = hybRight x y z .minus .plus .zero .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_5 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .zero .plus .minus = hybRight x y z .minus .plus .zero .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_21_6 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .zero .minus .zero = hybRight x y z .minus .plus .zero .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_7 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .zero .minus .plus = hybRight x y z .minus .plus .zero .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_21_8 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .zero .minus .minus = hybRight x y z .minus .plus .zero .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_9 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .plus .zero .zero = hybRight x y z .minus .plus .zero .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_10 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .plus .zero .plus = hybRight x y z .minus .plus .zero .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_11 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .plus .zero .minus = hybRight x y z .minus .plus .zero .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_21_12 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .plus .plus .zero = hybRight x y z .minus .plus .zero .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_13 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .plus .plus .plus = hybRight x y z .minus .plus .zero .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_14 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .plus .plus .minus = hybRight x y z .minus .plus .zero .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_15 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .plus .minus .zero = hybRight x y z .minus .plus .zero .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_21_16 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .plus .minus .plus = hybRight x y z .minus .plus .zero .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_17 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .plus .minus .minus = hybRight x y z .minus .plus .zero .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_18 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .minus .zero .zero = hybRight x y z .minus .plus .zero .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_19 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .minus .zero .plus = hybRight x y z .minus .plus .zero .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_21_20 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .minus .zero .minus = hybRight x y z .minus .plus .zero .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_21 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .minus .plus .zero = hybRight x y z .minus .plus .zero .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_21_22 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .minus .plus .plus = hybRight x y z .minus .plus .zero .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_23 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .minus .plus .minus = hybRight x y z .minus .plus .zero .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_24 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .minus .minus .zero = hybRight x y z .minus .plus .zero .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_25 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .minus .minus .plus = hybRight x y z .minus .plus .zero .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_21_26 (x y z : ℂ) :
    hybLeft x y z .minus .plus .zero .minus .minus .minus = hybRight x y z .minus .plus .zero .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_22_0 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .zero .zero .zero = hybRight x y z .minus .plus .plus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_1 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .zero .zero .plus = hybRight x y z .minus .plus .plus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_22_2 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .zero .zero .minus = hybRight x y z .minus .plus .plus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_3 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .zero .plus .zero = hybRight x y z .minus .plus .plus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13]
  all_goals ring

theorem hyb_entry_22_4 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .zero .plus .plus = hybRight x y z .minus .plus .plus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_5 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .zero .plus .minus = hybRight x y z .minus .plus .plus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_6 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .zero .minus .zero = hybRight x y z .minus .plus .plus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_7 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .zero .minus .plus = hybRight x y z .minus .plus .plus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_8 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .zero .minus .minus = hybRight x y z .minus .plus .plus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_22_9 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .plus .zero .zero = hybRight x y z .minus .plus .plus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_22_10 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .plus .zero .plus = hybRight x y z .minus .plus .plus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_11 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .plus .zero .minus = hybRight x y z .minus .plus .plus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_12 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .plus .plus .zero = hybRight x y z .minus .plus .plus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_13 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .plus .plus .plus = hybRight x y z .minus .plus .plus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_14 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .plus .plus .minus = hybRight x y z .minus .plus .plus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_22_15 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .plus .minus .zero = hybRight x y z .minus .plus .plus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_16 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .plus .minus .plus = hybRight x y z .minus .plus .plus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_22_17 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .plus .minus .minus = hybRight x y z .minus .plus .plus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_18 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .minus .zero .zero = hybRight x y z .minus .plus .plus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_19 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .minus .zero .plus = hybRight x y z .minus .plus .plus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_20 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .minus .zero .minus = hybRight x y z .minus .plus .plus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_22_21 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .minus .plus .zero = hybRight x y z .minus .plus .plus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_22 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .minus .plus .plus = hybRight x y z .minus .plus .plus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_22_23 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .minus .plus .minus = hybRight x y z .minus .plus .plus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_24 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .minus .minus .zero = hybRight x y z .minus .plus .plus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_22_25 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .minus .minus .plus = hybRight x y z .minus .plus .plus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_22_26 (x y z : ℂ) :
    hybLeft x y z .minus .plus .plus .minus .minus .minus = hybRight x y z .minus .plus .plus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_23_0 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .zero .zero .zero = hybRight x y z .minus .plus .minus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_1 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .zero .zero .plus = hybRight x y z .minus .plus .minus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_2 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .zero .zero .minus = hybRight x y z .minus .plus .minus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_23_3 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .zero .plus .zero = hybRight x y z .minus .plus .minus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_4 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .zero .plus .plus = hybRight x y z .minus .plus .minus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_5 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .zero .plus .minus = hybRight x y z .minus .plus .minus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_6 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .zero .minus .zero = hybRight x y z .minus .plus .minus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13]
  all_goals ring

theorem hyb_entry_23_7 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .zero .minus .plus = hybRight x y z .minus .plus .minus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_8 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .zero .minus .minus = hybRight x y z .minus .plus .minus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_9 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .plus .zero .zero = hybRight x y z .minus .plus .minus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_10 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .plus .zero .plus = hybRight x y z .minus .plus .minus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_23_11 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .plus .zero .minus = hybRight x y z .minus .plus .minus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_12 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .plus .plus .zero = hybRight x y z .minus .plus .minus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_23_13 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .plus .plus .plus = hybRight x y z .minus .plus .minus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_14 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .plus .plus .minus = hybRight x y z .minus .plus .minus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_15 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .plus .minus .zero = hybRight x y z .minus .plus .minus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_16 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .plus .minus .plus = hybRight x y z .minus .plus .minus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_17 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .plus .minus .minus = hybRight x y z .minus .plus .minus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_23_18 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .minus .zero .zero = hybRight x y z .minus .plus .minus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_23_19 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .minus .zero .plus = hybRight x y z .minus .plus .minus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_20 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .minus .zero .minus = hybRight x y z .minus .plus .minus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_21 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .minus .plus .zero = hybRight x y z .minus .plus .minus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_22 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .minus .plus .plus = hybRight x y z .minus .plus .minus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_23 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .minus .plus .minus = hybRight x y z .minus .plus .minus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_23_24 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .minus .minus .zero = hybRight x y z .minus .plus .minus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_23_25 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .minus .minus .plus = hybRight x y z .minus .plus .minus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_23_26 (x y z : ℂ) :
    hybLeft x y z .minus .plus .minus .minus .minus .minus = hybRight x y z .minus .plus .minus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_24_0 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .zero .zero .zero = hybRight x y z .minus .minus .zero .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_24_1 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .zero .zero .plus = hybRight x y z .minus .minus .zero .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_24_2 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .zero .zero .minus = hybRight x y z .minus .minus .zero .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_24_3 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .zero .plus .zero = hybRight x y z .minus .minus .zero .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_24_4 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .zero .plus .plus = hybRight x y z .minus .minus .zero .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_24_5 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .zero .plus .minus = hybRight x y z .minus .minus .zero .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_24_6 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .zero .minus .zero = hybRight x y z .minus .minus .zero .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_24_7 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .zero .minus .plus = hybRight x y z .minus .minus .zero .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_24_8 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .zero .minus .minus = hybRight x y z .minus .minus .zero .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_24_9 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .plus .zero .zero = hybRight x y z .minus .minus .zero .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_24_10 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .plus .zero .plus = hybRight x y z .minus .minus .zero .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_24_11 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .plus .zero .minus = hybRight x y z .minus .minus .zero .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_24_12 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .plus .plus .zero = hybRight x y z .minus .minus .zero .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_24_13 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .plus .plus .plus = hybRight x y z .minus .minus .zero .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_24_14 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .plus .plus .minus = hybRight x y z .minus .minus .zero .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_24_15 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .plus .minus .zero = hybRight x y z .minus .minus .zero .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_24_16 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .plus .minus .plus = hybRight x y z .minus .minus .zero .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_24_17 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .plus .minus .minus = hybRight x y z .minus .minus .zero .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_24_18 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .minus .zero .zero = hybRight x y z .minus .minus .zero .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_24_19 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .minus .zero .plus = hybRight x y z .minus .minus .zero .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_24_20 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .minus .zero .minus = hybRight x y z .minus .minus .zero .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14]
  all_goals ring

theorem hyb_entry_24_21 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .minus .plus .zero = hybRight x y z .minus .minus .zero .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_24_22 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .minus .plus .plus = hybRight x y z .minus .minus .zero .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_24_23 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .minus .plus .minus = hybRight x y z .minus .minus .zero .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_24_24 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .minus .minus .zero = hybRight x y z .minus .minus .zero .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_24_25 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .minus .minus .plus = hybRight x y z .minus .minus .zero .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_24_26 (x y z : ℂ) :
    hybLeft x y z .minus .minus .zero .minus .minus .minus = hybRight x y z .minus .minus .zero .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_0 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .zero .zero .zero = hybRight x y z .minus .minus .plus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_1 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .zero .zero .plus = hybRight x y z .minus .minus .plus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_2 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .zero .zero .minus = hybRight x y z .minus .minus .plus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_25_3 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .zero .plus .zero = hybRight x y z .minus .minus .plus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_4 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .zero .plus .plus = hybRight x y z .minus .minus .plus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_5 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .zero .plus .minus = hybRight x y z .minus .minus .plus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_6 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .zero .minus .zero = hybRight x y z .minus .minus .plus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13]
  all_goals ring

theorem hyb_entry_25_7 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .zero .minus .plus = hybRight x y z .minus .minus .plus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_8 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .zero .minus .minus = hybRight x y z .minus .minus .plus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_9 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .plus .zero .zero = hybRight x y z .minus .minus .plus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_10 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .plus .zero .plus = hybRight x y z .minus .minus .plus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_25_11 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .plus .zero .minus = hybRight x y z .minus .minus .plus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_12 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .plus .plus .zero = hybRight x y z .minus .minus .plus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_13 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .plus .plus .plus = hybRight x y z .minus .minus .plus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_14 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .plus .plus .minus = hybRight x y z .minus .minus .plus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_15 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .plus .minus .zero = hybRight x y z .minus .minus .plus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_16 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .plus .minus .plus = hybRight x y z .minus .minus .plus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_17 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .plus .minus .minus = hybRight x y z .minus .minus .plus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_entry_25_18 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .minus .zero .zero = hybRight x y z .minus .minus .plus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17]
  all_goals ring

theorem hyb_entry_25_19 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .minus .zero .plus = hybRight x y z .minus .minus .plus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_20 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .minus .zero .minus = hybRight x y z .minus .minus .plus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_21 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .minus .plus .zero = hybRight x y z .minus .minus .plus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_22 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .minus .plus .plus = hybRight x y z .minus .minus .plus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_23 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .minus .plus .minus = hybRight x y z .minus .minus .plus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_25_24 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .minus .minus .zero = hybRight x y z .minus .minus .plus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_25_25 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .minus .minus .plus = hybRight x y z .minus .minus .plus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

theorem hyb_entry_25_26 (x y z : ℂ) :
    hybLeft x y z .minus .minus .plus .minus .minus .minus = hybRight x y z .minus .minus .plus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_0 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .zero .zero .zero = hybRight x y z .minus .minus .minus .zero .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_1 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .zero .zero .plus = hybRight x y z .minus .minus .minus .zero .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_2 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .zero .zero .minus = hybRight x y z .minus .minus .minus .zero .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_3 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .zero .plus .zero = hybRight x y z .minus .minus .minus .zero .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_26_4 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .zero .plus .plus = hybRight x y z .minus .minus .minus .zero .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_26_5 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .zero .plus .minus = hybRight x y z .minus .minus .minus .zero .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_6 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .zero .minus .zero = hybRight x y z .minus .minus .minus .zero .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_7 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .zero .minus .plus = hybRight x y z .minus .minus .minus .zero .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_8 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .zero .minus .minus = hybRight x y z .minus .minus .minus .zero .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_9 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .plus .zero .zero = hybRight x y z .minus .minus .minus .plus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_10 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .plus .zero .plus = hybRight x y z .minus .minus .minus .plus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_26_11 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .plus .zero .minus = hybRight x y z .minus .minus .minus .plus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_12 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .plus .plus .zero = hybRight x y z .minus .minus .minus .plus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_26_13 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .plus .plus .plus = hybRight x y z .minus .minus .minus .plus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_26_14 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .plus .plus .minus = hybRight x y z .minus .minus .minus .plus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_15 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .plus .minus .zero = hybRight x y z .minus .minus .minus .plus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_16 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .plus .minus .plus = hybRight x y z .minus .minus .minus .plus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_17 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .plus .minus .minus = hybRight x y z .minus .minus .minus .plus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_18 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .minus .zero .zero = hybRight x y z .minus .minus .minus .minus .zero .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_19 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .minus .zero .plus = hybRight x y z .minus .minus .minus .minus .zero .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_20 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .minus .zero .minus = hybRight x y z .minus .minus .minus .minus .zero .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_21 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .minus .plus .zero = hybRight x y z .minus .minus .minus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

theorem hyb_entry_26_22 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .minus .plus .plus = hybRight x y z .minus .minus .minus .minus .plus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_23 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .minus .plus .minus = hybRight x y z .minus .minus .minus .minus .plus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_24 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .minus .minus .zero = hybRight x y z .minus .minus .minus .minus .minus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_25 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .minus .minus .plus = hybRight x y z .minus .minus .minus .minus .minus .plus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

theorem hyb_entry_26_26 (x y z : ℂ) :
    hybLeft x y z .minus .minus .minus .minus .minus .minus = hybRight x y z .minus .minus .minus .minus .minus .minus := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf

theorem hyb_output_0 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .zero .zero .zero d e f = hybRight x y z .zero .zero .zero d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_0_0 x y z
  · exact hyb_entry_0_1 x y z
  · exact hyb_entry_0_2 x y z
  · exact hyb_entry_0_3 x y z
  · exact hyb_entry_0_4 x y z
  · exact hyb_entry_0_5 x y z
  · exact hyb_entry_0_6 x y z
  · exact hyb_entry_0_7 x y z
  · exact hyb_entry_0_8 x y z
  · exact hyb_entry_0_9 x y z
  · exact hyb_entry_0_10 x y z
  · exact hyb_entry_0_11 x y z
  · exact hyb_entry_0_12 x y z
  · exact hyb_entry_0_13 x y z
  · exact hyb_entry_0_14 x y z
  · exact hyb_entry_0_15 x y z
  · exact hyb_entry_0_16 x y z
  · exact hyb_entry_0_17 x y z
  · exact hyb_entry_0_18 x y z
  · exact hyb_entry_0_19 x y z
  · exact hyb_entry_0_20 x y z
  · exact hyb_entry_0_21 x y z
  · exact hyb_entry_0_22 x y z
  · exact hyb_entry_0_23 x y z
  · exact hyb_entry_0_24 x y z
  · exact hyb_entry_0_25 x y z
  · exact hyb_entry_0_26 x y z

theorem hyb_output_1 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .zero .zero .plus d e f = hybRight x y z .zero .zero .plus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_1_0 x y z
  · exact hyb_entry_1_1 x y z
  · exact hyb_entry_1_2 x y z
  · exact hyb_entry_1_3 x y z
  · exact hyb_entry_1_4 x y z
  · exact hyb_entry_1_5 x y z
  · exact hyb_entry_1_6 x y z
  · exact hyb_entry_1_7 x y z
  · exact hyb_entry_1_8 x y z
  · exact hyb_entry_1_9 x y z
  · exact hyb_entry_1_10 x y z
  · exact hyb_entry_1_11 x y z
  · exact hyb_entry_1_12 x y z
  · exact hyb_entry_1_13 x y z
  · exact hyb_entry_1_14 x y z
  · exact hyb_entry_1_15 x y z
  · exact hyb_entry_1_16 x y z
  · exact hyb_entry_1_17 x y z
  · exact hyb_entry_1_18 x y z
  · exact hyb_entry_1_19 x y z
  · exact hyb_entry_1_20 x y z
  · exact hyb_entry_1_21 x y z
  · exact hyb_entry_1_22 x y z
  · exact hyb_entry_1_23 x y z
  · exact hyb_entry_1_24 x y z
  · exact hyb_entry_1_25 x y z
  · exact hyb_entry_1_26 x y z

theorem hyb_output_2 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .zero .zero .minus d e f = hybRight x y z .zero .zero .minus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_2_0 x y z
  · exact hyb_entry_2_1 x y z
  · exact hyb_entry_2_2 x y z
  · exact hyb_entry_2_3 x y z
  · exact hyb_entry_2_4 x y z
  · exact hyb_entry_2_5 x y z
  · exact hyb_entry_2_6 x y z
  · exact hyb_entry_2_7 x y z
  · exact hyb_entry_2_8 x y z
  · exact hyb_entry_2_9 x y z
  · exact hyb_entry_2_10 x y z
  · exact hyb_entry_2_11 x y z
  · exact hyb_entry_2_12 x y z
  · exact hyb_entry_2_13 x y z
  · exact hyb_entry_2_14 x y z
  · exact hyb_entry_2_15 x y z
  · exact hyb_entry_2_16 x y z
  · exact hyb_entry_2_17 x y z
  · exact hyb_entry_2_18 x y z
  · exact hyb_entry_2_19 x y z
  · exact hyb_entry_2_20 x y z
  · exact hyb_entry_2_21 x y z
  · exact hyb_entry_2_22 x y z
  · exact hyb_entry_2_23 x y z
  · exact hyb_entry_2_24 x y z
  · exact hyb_entry_2_25 x y z
  · exact hyb_entry_2_26 x y z

theorem hyb_output_3 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .zero .plus .zero d e f = hybRight x y z .zero .plus .zero d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_3_0 x y z
  · exact hyb_entry_3_1 x y z
  · exact hyb_entry_3_2 x y z
  · exact hyb_entry_3_3 x y z
  · exact hyb_entry_3_4 x y z
  · exact hyb_entry_3_5 x y z
  · exact hyb_entry_3_6 x y z
  · exact hyb_entry_3_7 x y z
  · exact hyb_entry_3_8 x y z
  · exact hyb_entry_3_9 x y z
  · exact hyb_entry_3_10 x y z
  · exact hyb_entry_3_11 x y z
  · exact hyb_entry_3_12 x y z
  · exact hyb_entry_3_13 x y z
  · exact hyb_entry_3_14 x y z
  · exact hyb_entry_3_15 x y z
  · exact hyb_entry_3_16 x y z
  · exact hyb_entry_3_17 x y z
  · exact hyb_entry_3_18 x y z
  · exact hyb_entry_3_19 x y z
  · exact hyb_entry_3_20 x y z
  · exact hyb_entry_3_21 x y z
  · exact hyb_entry_3_22 x y z
  · exact hyb_entry_3_23 x y z
  · exact hyb_entry_3_24 x y z
  · exact hyb_entry_3_25 x y z
  · exact hyb_entry_3_26 x y z

theorem hyb_output_4 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .zero .plus .plus d e f = hybRight x y z .zero .plus .plus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_4_0 x y z
  · exact hyb_entry_4_1 x y z
  · exact hyb_entry_4_2 x y z
  · exact hyb_entry_4_3 x y z
  · exact hyb_entry_4_4 x y z
  · exact hyb_entry_4_5 x y z
  · exact hyb_entry_4_6 x y z
  · exact hyb_entry_4_7 x y z
  · exact hyb_entry_4_8 x y z
  · exact hyb_entry_4_9 x y z
  · exact hyb_entry_4_10 x y z
  · exact hyb_entry_4_11 x y z
  · exact hyb_entry_4_12 x y z
  · exact hyb_entry_4_13 x y z
  · exact hyb_entry_4_14 x y z
  · exact hyb_entry_4_15 x y z
  · exact hyb_entry_4_16 x y z
  · exact hyb_entry_4_17 x y z
  · exact hyb_entry_4_18 x y z
  · exact hyb_entry_4_19 x y z
  · exact hyb_entry_4_20 x y z
  · exact hyb_entry_4_21 x y z
  · exact hyb_entry_4_22 x y z
  · exact hyb_entry_4_23 x y z
  · exact hyb_entry_4_24 x y z
  · exact hyb_entry_4_25 x y z
  · exact hyb_entry_4_26 x y z

theorem hyb_output_5 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .zero .plus .minus d e f = hybRight x y z .zero .plus .minus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_5_0 x y z
  · exact hyb_entry_5_1 x y z
  · exact hyb_entry_5_2 x y z
  · exact hyb_entry_5_3 x y z
  · exact hyb_entry_5_4 x y z
  · exact hyb_entry_5_5 x y z
  · exact hyb_entry_5_6 x y z
  · exact hyb_entry_5_7 x y z
  · exact hyb_entry_5_8 x y z
  · exact hyb_entry_5_9 x y z
  · exact hyb_entry_5_10 x y z
  · exact hyb_entry_5_11 x y z
  · exact hyb_entry_5_12 x y z
  · exact hyb_entry_5_13 x y z
  · exact hyb_entry_5_14 x y z
  · exact hyb_entry_5_15 x y z
  · exact hyb_entry_5_16 x y z
  · exact hyb_entry_5_17 x y z
  · exact hyb_entry_5_18 x y z
  · exact hyb_entry_5_19 x y z
  · exact hyb_entry_5_20 x y z
  · exact hyb_entry_5_21 x y z
  · exact hyb_entry_5_22 x y z
  · exact hyb_entry_5_23 x y z
  · exact hyb_entry_5_24 x y z
  · exact hyb_entry_5_25 x y z
  · exact hyb_entry_5_26 x y z

theorem hyb_output_6 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .zero .minus .zero d e f = hybRight x y z .zero .minus .zero d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_6_0 x y z
  · exact hyb_entry_6_1 x y z
  · exact hyb_entry_6_2 x y z
  · exact hyb_entry_6_3 x y z
  · exact hyb_entry_6_4 x y z
  · exact hyb_entry_6_5 x y z
  · exact hyb_entry_6_6 x y z
  · exact hyb_entry_6_7 x y z
  · exact hyb_entry_6_8 x y z
  · exact hyb_entry_6_9 x y z
  · exact hyb_entry_6_10 x y z
  · exact hyb_entry_6_11 x y z
  · exact hyb_entry_6_12 x y z
  · exact hyb_entry_6_13 x y z
  · exact hyb_entry_6_14 x y z
  · exact hyb_entry_6_15 x y z
  · exact hyb_entry_6_16 x y z
  · exact hyb_entry_6_17 x y z
  · exact hyb_entry_6_18 x y z
  · exact hyb_entry_6_19 x y z
  · exact hyb_entry_6_20 x y z
  · exact hyb_entry_6_21 x y z
  · exact hyb_entry_6_22 x y z
  · exact hyb_entry_6_23 x y z
  · exact hyb_entry_6_24 x y z
  · exact hyb_entry_6_25 x y z
  · exact hyb_entry_6_26 x y z

theorem hyb_output_7 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .zero .minus .plus d e f = hybRight x y z .zero .minus .plus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_7_0 x y z
  · exact hyb_entry_7_1 x y z
  · exact hyb_entry_7_2 x y z
  · exact hyb_entry_7_3 x y z
  · exact hyb_entry_7_4 x y z
  · exact hyb_entry_7_5 x y z
  · exact hyb_entry_7_6 x y z
  · exact hyb_entry_7_7 x y z
  · exact hyb_entry_7_8 x y z
  · exact hyb_entry_7_9 x y z
  · exact hyb_entry_7_10 x y z
  · exact hyb_entry_7_11 x y z
  · exact hyb_entry_7_12 x y z
  · exact hyb_entry_7_13 x y z
  · exact hyb_entry_7_14 x y z
  · exact hyb_entry_7_15 x y z
  · exact hyb_entry_7_16 x y z
  · exact hyb_entry_7_17 x y z
  · exact hyb_entry_7_18 x y z
  · exact hyb_entry_7_19 x y z
  · exact hyb_entry_7_20 x y z
  · exact hyb_entry_7_21 x y z
  · exact hyb_entry_7_22 x y z
  · exact hyb_entry_7_23 x y z
  · exact hyb_entry_7_24 x y z
  · exact hyb_entry_7_25 x y z
  · exact hyb_entry_7_26 x y z

theorem hyb_output_8 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .zero .minus .minus d e f = hybRight x y z .zero .minus .minus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_8_0 x y z
  · exact hyb_entry_8_1 x y z
  · exact hyb_entry_8_2 x y z
  · exact hyb_entry_8_3 x y z
  · exact hyb_entry_8_4 x y z
  · exact hyb_entry_8_5 x y z
  · exact hyb_entry_8_6 x y z
  · exact hyb_entry_8_7 x y z
  · exact hyb_entry_8_8 x y z
  · exact hyb_entry_8_9 x y z
  · exact hyb_entry_8_10 x y z
  · exact hyb_entry_8_11 x y z
  · exact hyb_entry_8_12 x y z
  · exact hyb_entry_8_13 x y z
  · exact hyb_entry_8_14 x y z
  · exact hyb_entry_8_15 x y z
  · exact hyb_entry_8_16 x y z
  · exact hyb_entry_8_17 x y z
  · exact hyb_entry_8_18 x y z
  · exact hyb_entry_8_19 x y z
  · exact hyb_entry_8_20 x y z
  · exact hyb_entry_8_21 x y z
  · exact hyb_entry_8_22 x y z
  · exact hyb_entry_8_23 x y z
  · exact hyb_entry_8_24 x y z
  · exact hyb_entry_8_25 x y z
  · exact hyb_entry_8_26 x y z

theorem hyb_output_9 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .plus .zero .zero d e f = hybRight x y z .plus .zero .zero d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_9_0 x y z
  · exact hyb_entry_9_1 x y z
  · exact hyb_entry_9_2 x y z
  · exact hyb_entry_9_3 x y z
  · exact hyb_entry_9_4 x y z
  · exact hyb_entry_9_5 x y z
  · exact hyb_entry_9_6 x y z
  · exact hyb_entry_9_7 x y z
  · exact hyb_entry_9_8 x y z
  · exact hyb_entry_9_9 x y z
  · exact hyb_entry_9_10 x y z
  · exact hyb_entry_9_11 x y z
  · exact hyb_entry_9_12 x y z
  · exact hyb_entry_9_13 x y z
  · exact hyb_entry_9_14 x y z
  · exact hyb_entry_9_15 x y z
  · exact hyb_entry_9_16 x y z
  · exact hyb_entry_9_17 x y z
  · exact hyb_entry_9_18 x y z
  · exact hyb_entry_9_19 x y z
  · exact hyb_entry_9_20 x y z
  · exact hyb_entry_9_21 x y z
  · exact hyb_entry_9_22 x y z
  · exact hyb_entry_9_23 x y z
  · exact hyb_entry_9_24 x y z
  · exact hyb_entry_9_25 x y z
  · exact hyb_entry_9_26 x y z

theorem hyb_output_10 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .plus .zero .plus d e f = hybRight x y z .plus .zero .plus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_10_0 x y z
  · exact hyb_entry_10_1 x y z
  · exact hyb_entry_10_2 x y z
  · exact hyb_entry_10_3 x y z
  · exact hyb_entry_10_4 x y z
  · exact hyb_entry_10_5 x y z
  · exact hyb_entry_10_6 x y z
  · exact hyb_entry_10_7 x y z
  · exact hyb_entry_10_8 x y z
  · exact hyb_entry_10_9 x y z
  · exact hyb_entry_10_10 x y z
  · exact hyb_entry_10_11 x y z
  · exact hyb_entry_10_12 x y z
  · exact hyb_entry_10_13 x y z
  · exact hyb_entry_10_14 x y z
  · exact hyb_entry_10_15 x y z
  · exact hyb_entry_10_16 x y z
  · exact hyb_entry_10_17 x y z
  · exact hyb_entry_10_18 x y z
  · exact hyb_entry_10_19 x y z
  · exact hyb_entry_10_20 x y z
  · exact hyb_entry_10_21 x y z
  · exact hyb_entry_10_22 x y z
  · exact hyb_entry_10_23 x y z
  · exact hyb_entry_10_24 x y z
  · exact hyb_entry_10_25 x y z
  · exact hyb_entry_10_26 x y z

theorem hyb_output_11 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .plus .zero .minus d e f = hybRight x y z .plus .zero .minus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_11_0 x y z
  · exact hyb_entry_11_1 x y z
  · exact hyb_entry_11_2 x y z
  · exact hyb_entry_11_3 x y z
  · exact hyb_entry_11_4 x y z
  · exact hyb_entry_11_5 x y z
  · exact hyb_entry_11_6 x y z
  · exact hyb_entry_11_7 x y z
  · exact hyb_entry_11_8 x y z
  · exact hyb_entry_11_9 x y z
  · exact hyb_entry_11_10 x y z
  · exact hyb_entry_11_11 x y z
  · exact hyb_entry_11_12 x y z
  · exact hyb_entry_11_13 x y z
  · exact hyb_entry_11_14 x y z
  · exact hyb_entry_11_15 x y z
  · exact hyb_entry_11_16 x y z
  · exact hyb_entry_11_17 x y z
  · exact hyb_entry_11_18 x y z
  · exact hyb_entry_11_19 x y z
  · exact hyb_entry_11_20 x y z
  · exact hyb_entry_11_21 x y z
  · exact hyb_entry_11_22 x y z
  · exact hyb_entry_11_23 x y z
  · exact hyb_entry_11_24 x y z
  · exact hyb_entry_11_25 x y z
  · exact hyb_entry_11_26 x y z

theorem hyb_output_12 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .plus .plus .zero d e f = hybRight x y z .plus .plus .zero d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_12_0 x y z
  · exact hyb_entry_12_1 x y z
  · exact hyb_entry_12_2 x y z
  · exact hyb_entry_12_3 x y z
  · exact hyb_entry_12_4 x y z
  · exact hyb_entry_12_5 x y z
  · exact hyb_entry_12_6 x y z
  · exact hyb_entry_12_7 x y z
  · exact hyb_entry_12_8 x y z
  · exact hyb_entry_12_9 x y z
  · exact hyb_entry_12_10 x y z
  · exact hyb_entry_12_11 x y z
  · exact hyb_entry_12_12 x y z
  · exact hyb_entry_12_13 x y z
  · exact hyb_entry_12_14 x y z
  · exact hyb_entry_12_15 x y z
  · exact hyb_entry_12_16 x y z
  · exact hyb_entry_12_17 x y z
  · exact hyb_entry_12_18 x y z
  · exact hyb_entry_12_19 x y z
  · exact hyb_entry_12_20 x y z
  · exact hyb_entry_12_21 x y z
  · exact hyb_entry_12_22 x y z
  · exact hyb_entry_12_23 x y z
  · exact hyb_entry_12_24 x y z
  · exact hyb_entry_12_25 x y z
  · exact hyb_entry_12_26 x y z

theorem hyb_output_13 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .plus .plus .plus d e f = hybRight x y z .plus .plus .plus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_13_0 x y z
  · exact hyb_entry_13_1 x y z
  · exact hyb_entry_13_2 x y z
  · exact hyb_entry_13_3 x y z
  · exact hyb_entry_13_4 x y z
  · exact hyb_entry_13_5 x y z
  · exact hyb_entry_13_6 x y z
  · exact hyb_entry_13_7 x y z
  · exact hyb_entry_13_8 x y z
  · exact hyb_entry_13_9 x y z
  · exact hyb_entry_13_10 x y z
  · exact hyb_entry_13_11 x y z
  · exact hyb_entry_13_12 x y z
  · exact hyb_entry_13_13 x y z
  · exact hyb_entry_13_14 x y z
  · exact hyb_entry_13_15 x y z
  · exact hyb_entry_13_16 x y z
  · exact hyb_entry_13_17 x y z
  · exact hyb_entry_13_18 x y z
  · exact hyb_entry_13_19 x y z
  · exact hyb_entry_13_20 x y z
  · exact hyb_entry_13_21 x y z
  · exact hyb_entry_13_22 x y z
  · exact hyb_entry_13_23 x y z
  · exact hyb_entry_13_24 x y z
  · exact hyb_entry_13_25 x y z
  · exact hyb_entry_13_26 x y z

theorem hyb_output_14 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .plus .plus .minus d e f = hybRight x y z .plus .plus .minus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_14_0 x y z
  · exact hyb_entry_14_1 x y z
  · exact hyb_entry_14_2 x y z
  · exact hyb_entry_14_3 x y z
  · exact hyb_entry_14_4 x y z
  · exact hyb_entry_14_5 x y z
  · exact hyb_entry_14_6 x y z
  · exact hyb_entry_14_7 x y z
  · exact hyb_entry_14_8 x y z
  · exact hyb_entry_14_9 x y z
  · exact hyb_entry_14_10 x y z
  · exact hyb_entry_14_11 x y z
  · exact hyb_entry_14_12 x y z
  · exact hyb_entry_14_13 x y z
  · exact hyb_entry_14_14 x y z
  · exact hyb_entry_14_15 x y z
  · exact hyb_entry_14_16 x y z
  · exact hyb_entry_14_17 x y z
  · exact hyb_entry_14_18 x y z
  · exact hyb_entry_14_19 x y z
  · exact hyb_entry_14_20 x y z
  · exact hyb_entry_14_21 x y z
  · exact hyb_entry_14_22 x y z
  · exact hyb_entry_14_23 x y z
  · exact hyb_entry_14_24 x y z
  · exact hyb_entry_14_25 x y z
  · exact hyb_entry_14_26 x y z

theorem hyb_output_15 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .plus .minus .zero d e f = hybRight x y z .plus .minus .zero d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_15_0 x y z
  · exact hyb_entry_15_1 x y z
  · exact hyb_entry_15_2 x y z
  · exact hyb_entry_15_3 x y z
  · exact hyb_entry_15_4 x y z
  · exact hyb_entry_15_5 x y z
  · exact hyb_entry_15_6 x y z
  · exact hyb_entry_15_7 x y z
  · exact hyb_entry_15_8 x y z
  · exact hyb_entry_15_9 x y z
  · exact hyb_entry_15_10 x y z
  · exact hyb_entry_15_11 x y z
  · exact hyb_entry_15_12 x y z
  · exact hyb_entry_15_13 x y z
  · exact hyb_entry_15_14 x y z
  · exact hyb_entry_15_15 x y z
  · exact hyb_entry_15_16 x y z
  · exact hyb_entry_15_17 x y z
  · exact hyb_entry_15_18 x y z
  · exact hyb_entry_15_19 x y z
  · exact hyb_entry_15_20 x y z
  · exact hyb_entry_15_21 x y z
  · exact hyb_entry_15_22 x y z
  · exact hyb_entry_15_23 x y z
  · exact hyb_entry_15_24 x y z
  · exact hyb_entry_15_25 x y z
  · exact hyb_entry_15_26 x y z

theorem hyb_output_16 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .plus .minus .plus d e f = hybRight x y z .plus .minus .plus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_16_0 x y z
  · exact hyb_entry_16_1 x y z
  · exact hyb_entry_16_2 x y z
  · exact hyb_entry_16_3 x y z
  · exact hyb_entry_16_4 x y z
  · exact hyb_entry_16_5 x y z
  · exact hyb_entry_16_6 x y z
  · exact hyb_entry_16_7 x y z
  · exact hyb_entry_16_8 x y z
  · exact hyb_entry_16_9 x y z
  · exact hyb_entry_16_10 x y z
  · exact hyb_entry_16_11 x y z
  · exact hyb_entry_16_12 x y z
  · exact hyb_entry_16_13 x y z
  · exact hyb_entry_16_14 x y z
  · exact hyb_entry_16_15 x y z
  · exact hyb_entry_16_16 x y z
  · exact hyb_entry_16_17 x y z
  · exact hyb_entry_16_18 x y z
  · exact hyb_entry_16_19 x y z
  · exact hyb_entry_16_20 x y z
  · exact hyb_entry_16_21 x y z
  · exact hyb_entry_16_22 x y z
  · exact hyb_entry_16_23 x y z
  · exact hyb_entry_16_24 x y z
  · exact hyb_entry_16_25 x y z
  · exact hyb_entry_16_26 x y z

theorem hyb_output_17 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .plus .minus .minus d e f = hybRight x y z .plus .minus .minus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_17_0 x y z
  · exact hyb_entry_17_1 x y z
  · exact hyb_entry_17_2 x y z
  · exact hyb_entry_17_3 x y z
  · exact hyb_entry_17_4 x y z
  · exact hyb_entry_17_5 x y z
  · exact hyb_entry_17_6 x y z
  · exact hyb_entry_17_7 x y z
  · exact hyb_entry_17_8 x y z
  · exact hyb_entry_17_9 x y z
  · exact hyb_entry_17_10 x y z
  · exact hyb_entry_17_11 x y z
  · exact hyb_entry_17_12 x y z
  · exact hyb_entry_17_13 x y z
  · exact hyb_entry_17_14 x y z
  · exact hyb_entry_17_15 x y z
  · exact hyb_entry_17_16 x y z
  · exact hyb_entry_17_17 x y z
  · exact hyb_entry_17_18 x y z
  · exact hyb_entry_17_19 x y z
  · exact hyb_entry_17_20 x y z
  · exact hyb_entry_17_21 x y z
  · exact hyb_entry_17_22 x y z
  · exact hyb_entry_17_23 x y z
  · exact hyb_entry_17_24 x y z
  · exact hyb_entry_17_25 x y z
  · exact hyb_entry_17_26 x y z

theorem hyb_output_18 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .minus .zero .zero d e f = hybRight x y z .minus .zero .zero d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_18_0 x y z
  · exact hyb_entry_18_1 x y z
  · exact hyb_entry_18_2 x y z
  · exact hyb_entry_18_3 x y z
  · exact hyb_entry_18_4 x y z
  · exact hyb_entry_18_5 x y z
  · exact hyb_entry_18_6 x y z
  · exact hyb_entry_18_7 x y z
  · exact hyb_entry_18_8 x y z
  · exact hyb_entry_18_9 x y z
  · exact hyb_entry_18_10 x y z
  · exact hyb_entry_18_11 x y z
  · exact hyb_entry_18_12 x y z
  · exact hyb_entry_18_13 x y z
  · exact hyb_entry_18_14 x y z
  · exact hyb_entry_18_15 x y z
  · exact hyb_entry_18_16 x y z
  · exact hyb_entry_18_17 x y z
  · exact hyb_entry_18_18 x y z
  · exact hyb_entry_18_19 x y z
  · exact hyb_entry_18_20 x y z
  · exact hyb_entry_18_21 x y z
  · exact hyb_entry_18_22 x y z
  · exact hyb_entry_18_23 x y z
  · exact hyb_entry_18_24 x y z
  · exact hyb_entry_18_25 x y z
  · exact hyb_entry_18_26 x y z

theorem hyb_output_19 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .minus .zero .plus d e f = hybRight x y z .minus .zero .plus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_19_0 x y z
  · exact hyb_entry_19_1 x y z
  · exact hyb_entry_19_2 x y z
  · exact hyb_entry_19_3 x y z
  · exact hyb_entry_19_4 x y z
  · exact hyb_entry_19_5 x y z
  · exact hyb_entry_19_6 x y z
  · exact hyb_entry_19_7 x y z
  · exact hyb_entry_19_8 x y z
  · exact hyb_entry_19_9 x y z
  · exact hyb_entry_19_10 x y z
  · exact hyb_entry_19_11 x y z
  · exact hyb_entry_19_12 x y z
  · exact hyb_entry_19_13 x y z
  · exact hyb_entry_19_14 x y z
  · exact hyb_entry_19_15 x y z
  · exact hyb_entry_19_16 x y z
  · exact hyb_entry_19_17 x y z
  · exact hyb_entry_19_18 x y z
  · exact hyb_entry_19_19 x y z
  · exact hyb_entry_19_20 x y z
  · exact hyb_entry_19_21 x y z
  · exact hyb_entry_19_22 x y z
  · exact hyb_entry_19_23 x y z
  · exact hyb_entry_19_24 x y z
  · exact hyb_entry_19_25 x y z
  · exact hyb_entry_19_26 x y z

theorem hyb_output_20 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .minus .zero .minus d e f = hybRight x y z .minus .zero .minus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_20_0 x y z
  · exact hyb_entry_20_1 x y z
  · exact hyb_entry_20_2 x y z
  · exact hyb_entry_20_3 x y z
  · exact hyb_entry_20_4 x y z
  · exact hyb_entry_20_5 x y z
  · exact hyb_entry_20_6 x y z
  · exact hyb_entry_20_7 x y z
  · exact hyb_entry_20_8 x y z
  · exact hyb_entry_20_9 x y z
  · exact hyb_entry_20_10 x y z
  · exact hyb_entry_20_11 x y z
  · exact hyb_entry_20_12 x y z
  · exact hyb_entry_20_13 x y z
  · exact hyb_entry_20_14 x y z
  · exact hyb_entry_20_15 x y z
  · exact hyb_entry_20_16 x y z
  · exact hyb_entry_20_17 x y z
  · exact hyb_entry_20_18 x y z
  · exact hyb_entry_20_19 x y z
  · exact hyb_entry_20_20 x y z
  · exact hyb_entry_20_21 x y z
  · exact hyb_entry_20_22 x y z
  · exact hyb_entry_20_23 x y z
  · exact hyb_entry_20_24 x y z
  · exact hyb_entry_20_25 x y z
  · exact hyb_entry_20_26 x y z

theorem hyb_output_21 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .minus .plus .zero d e f = hybRight x y z .minus .plus .zero d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_21_0 x y z
  · exact hyb_entry_21_1 x y z
  · exact hyb_entry_21_2 x y z
  · exact hyb_entry_21_3 x y z
  · exact hyb_entry_21_4 x y z
  · exact hyb_entry_21_5 x y z
  · exact hyb_entry_21_6 x y z
  · exact hyb_entry_21_7 x y z
  · exact hyb_entry_21_8 x y z
  · exact hyb_entry_21_9 x y z
  · exact hyb_entry_21_10 x y z
  · exact hyb_entry_21_11 x y z
  · exact hyb_entry_21_12 x y z
  · exact hyb_entry_21_13 x y z
  · exact hyb_entry_21_14 x y z
  · exact hyb_entry_21_15 x y z
  · exact hyb_entry_21_16 x y z
  · exact hyb_entry_21_17 x y z
  · exact hyb_entry_21_18 x y z
  · exact hyb_entry_21_19 x y z
  · exact hyb_entry_21_20 x y z
  · exact hyb_entry_21_21 x y z
  · exact hyb_entry_21_22 x y z
  · exact hyb_entry_21_23 x y z
  · exact hyb_entry_21_24 x y z
  · exact hyb_entry_21_25 x y z
  · exact hyb_entry_21_26 x y z

theorem hyb_output_22 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .minus .plus .plus d e f = hybRight x y z .minus .plus .plus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_22_0 x y z
  · exact hyb_entry_22_1 x y z
  · exact hyb_entry_22_2 x y z
  · exact hyb_entry_22_3 x y z
  · exact hyb_entry_22_4 x y z
  · exact hyb_entry_22_5 x y z
  · exact hyb_entry_22_6 x y z
  · exact hyb_entry_22_7 x y z
  · exact hyb_entry_22_8 x y z
  · exact hyb_entry_22_9 x y z
  · exact hyb_entry_22_10 x y z
  · exact hyb_entry_22_11 x y z
  · exact hyb_entry_22_12 x y z
  · exact hyb_entry_22_13 x y z
  · exact hyb_entry_22_14 x y z
  · exact hyb_entry_22_15 x y z
  · exact hyb_entry_22_16 x y z
  · exact hyb_entry_22_17 x y z
  · exact hyb_entry_22_18 x y z
  · exact hyb_entry_22_19 x y z
  · exact hyb_entry_22_20 x y z
  · exact hyb_entry_22_21 x y z
  · exact hyb_entry_22_22 x y z
  · exact hyb_entry_22_23 x y z
  · exact hyb_entry_22_24 x y z
  · exact hyb_entry_22_25 x y z
  · exact hyb_entry_22_26 x y z

theorem hyb_output_23 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .minus .plus .minus d e f = hybRight x y z .minus .plus .minus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_23_0 x y z
  · exact hyb_entry_23_1 x y z
  · exact hyb_entry_23_2 x y z
  · exact hyb_entry_23_3 x y z
  · exact hyb_entry_23_4 x y z
  · exact hyb_entry_23_5 x y z
  · exact hyb_entry_23_6 x y z
  · exact hyb_entry_23_7 x y z
  · exact hyb_entry_23_8 x y z
  · exact hyb_entry_23_9 x y z
  · exact hyb_entry_23_10 x y z
  · exact hyb_entry_23_11 x y z
  · exact hyb_entry_23_12 x y z
  · exact hyb_entry_23_13 x y z
  · exact hyb_entry_23_14 x y z
  · exact hyb_entry_23_15 x y z
  · exact hyb_entry_23_16 x y z
  · exact hyb_entry_23_17 x y z
  · exact hyb_entry_23_18 x y z
  · exact hyb_entry_23_19 x y z
  · exact hyb_entry_23_20 x y z
  · exact hyb_entry_23_21 x y z
  · exact hyb_entry_23_22 x y z
  · exact hyb_entry_23_23 x y z
  · exact hyb_entry_23_24 x y z
  · exact hyb_entry_23_25 x y z
  · exact hyb_entry_23_26 x y z

theorem hyb_output_24 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .minus .minus .zero d e f = hybRight x y z .minus .minus .zero d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_24_0 x y z
  · exact hyb_entry_24_1 x y z
  · exact hyb_entry_24_2 x y z
  · exact hyb_entry_24_3 x y z
  · exact hyb_entry_24_4 x y z
  · exact hyb_entry_24_5 x y z
  · exact hyb_entry_24_6 x y z
  · exact hyb_entry_24_7 x y z
  · exact hyb_entry_24_8 x y z
  · exact hyb_entry_24_9 x y z
  · exact hyb_entry_24_10 x y z
  · exact hyb_entry_24_11 x y z
  · exact hyb_entry_24_12 x y z
  · exact hyb_entry_24_13 x y z
  · exact hyb_entry_24_14 x y z
  · exact hyb_entry_24_15 x y z
  · exact hyb_entry_24_16 x y z
  · exact hyb_entry_24_17 x y z
  · exact hyb_entry_24_18 x y z
  · exact hyb_entry_24_19 x y z
  · exact hyb_entry_24_20 x y z
  · exact hyb_entry_24_21 x y z
  · exact hyb_entry_24_22 x y z
  · exact hyb_entry_24_23 x y z
  · exact hyb_entry_24_24 x y z
  · exact hyb_entry_24_25 x y z
  · exact hyb_entry_24_26 x y z

theorem hyb_output_25 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .minus .minus .plus d e f = hybRight x y z .minus .minus .plus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_25_0 x y z
  · exact hyb_entry_25_1 x y z
  · exact hyb_entry_25_2 x y z
  · exact hyb_entry_25_3 x y z
  · exact hyb_entry_25_4 x y z
  · exact hyb_entry_25_5 x y z
  · exact hyb_entry_25_6 x y z
  · exact hyb_entry_25_7 x y z
  · exact hyb_entry_25_8 x y z
  · exact hyb_entry_25_9 x y z
  · exact hyb_entry_25_10 x y z
  · exact hyb_entry_25_11 x y z
  · exact hyb_entry_25_12 x y z
  · exact hyb_entry_25_13 x y z
  · exact hyb_entry_25_14 x y z
  · exact hyb_entry_25_15 x y z
  · exact hyb_entry_25_16 x y z
  · exact hyb_entry_25_17 x y z
  · exact hyb_entry_25_18 x y z
  · exact hyb_entry_25_19 x y z
  · exact hyb_entry_25_20 x y z
  · exact hyb_entry_25_21 x y z
  · exact hyb_entry_25_22 x y z
  · exact hyb_entry_25_23 x y z
  · exact hyb_entry_25_24 x y z
  · exact hyb_entry_25_25 x y z
  · exact hyb_entry_25_26 x y z

theorem hyb_output_26 (x y z : ℂ) (d e f : Spin) :
    hybLeft x y z .minus .minus .minus d e f = hybRight x y z .minus .minus .minus d e f := by
  cases d <;> cases e <;> cases f
  · exact hyb_entry_26_0 x y z
  · exact hyb_entry_26_1 x y z
  · exact hyb_entry_26_2 x y z
  · exact hyb_entry_26_3 x y z
  · exact hyb_entry_26_4 x y z
  · exact hyb_entry_26_5 x y z
  · exact hyb_entry_26_6 x y z
  · exact hyb_entry_26_7 x y z
  · exact hyb_entry_26_8 x y z
  · exact hyb_entry_26_9 x y z
  · exact hyb_entry_26_10 x y z
  · exact hyb_entry_26_11 x y z
  · exact hyb_entry_26_12 x y z
  · exact hyb_entry_26_13 x y z
  · exact hyb_entry_26_14 x y z
  · exact hyb_entry_26_15 x y z
  · exact hyb_entry_26_16 x y z
  · exact hyb_entry_26_17 x y z
  · exact hyb_entry_26_18 x y z
  · exact hyb_entry_26_19 x y z
  · exact hyb_entry_26_20 x y z
  · exact hyb_entry_26_21 x y z
  · exact hyb_entry_26_22 x y z
  · exact hyb_entry_26_23 x y z
  · exact hyb_entry_26_24 x y z
  · exact hyb_entry_26_25 x y z
  · exact hyb_entry_26_26 x y z

 

theorem homogeneous_yang_baxter_coefficients (x y z : ℂ) (a b c d e f : Spin) :
    hybLeft x y z a b c d e f = hybRight x y z a b c d e f := by
  cases a <;> cases b <;> cases c
  · exact hyb_output_0 x y z d e f
  · exact hyb_output_1 x y z d e f
  · exact hyb_output_2 x y z d e f
  · exact hyb_output_3 x y z d e f
  · exact hyb_output_4 x y z d e f
  · exact hyb_output_5 x y z d e f
  · exact hyb_output_6 x y z d e f
  · exact hyb_output_7 x y z d e f
  · exact hyb_output_8 x y z d e f
  · exact hyb_output_9 x y z d e f
  · exact hyb_output_10 x y z d e f
  · exact hyb_output_11 x y z d e f
  · exact hyb_output_12 x y z d e f
  · exact hyb_output_13 x y z d e f
  · exact hyb_output_14 x y z d e f
  · exact hyb_output_15 x y z d e f
  · exact hyb_output_16 x y z d e f
  · exact hyb_output_17 x y z d e f
  · exact hyb_output_18 x y z d e f
  · exact hyb_output_19 x y z d e f
  · exact hyb_output_20 x y z d e f
  · exact hyb_output_21 x y z d e f
  · exact hyb_output_22 x y z d e f
  · exact hyb_output_23 x y z d e f
  · exact hyb_output_24 x y z d e f
  · exact hyb_output_25 x y z d e f
  · exact hyb_output_26 x y z d e f

end PolynomialVacuumAlgebra

end OAI
