import OAI.Combinatorics.PolynomialVacuum.Algebra.Table
import OAI.Combinatorics.PolynomialVacuum.Algebra.Ring

namespace OAI

namespace PolynomialVacuumAlgebra
noncomputable def homogeneousUncupLeft (x y : ℂ) (a b c h : Spin) : ℂ :=
  exchangeDenominator (T*x) y * ∑ k : Spin,
    exchangeNumerator y x (a,b) (h,k) * cup (k,c)
noncomputable def homogeneousUncupRight (x y : ℂ) (a b c h : Spin) : ℂ :=
  exchangeDenominator y x * ∑ k : Spin,
    exchangeNumerator (T*x) y (b,c) (k,h) * cup (a,k)
theorem homogeneous_uncup_entry_0_0 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .zero .zero .zero = homogeneousUncupRight x y .zero .zero .zero .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_0_1 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .zero .zero .plus = homogeneousUncupRight x y .zero .zero .zero .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_0_2 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .zero .zero .minus = homogeneousUncupRight x y .zero .zero .zero .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_1_0 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .zero .plus .zero = homogeneousUncupRight x y .zero .zero .plus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_1_1 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .zero .plus .plus = homogeneousUncupRight x y .zero .zero .plus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_1_2 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .zero .plus .minus = homogeneousUncupRight x y .zero .zero .plus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_2_0 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .zero .minus .zero = homogeneousUncupRight x y .zero .zero .minus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_2_1 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .zero .minus .plus = homogeneousUncupRight x y .zero .zero .minus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_2_2 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .zero .minus .minus = homogeneousUncupRight x y .zero .zero .minus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_3_0 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .plus .zero .zero = homogeneousUncupRight x y .zero .plus .zero .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_3_1 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .plus .zero .plus = homogeneousUncupRight x y .zero .plus .zero .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_3_2 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .plus .zero .minus = homogeneousUncupRight x y .zero .plus .zero .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_4_0 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .plus .plus .zero = homogeneousUncupRight x y .zero .plus .plus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_4_1 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .plus .plus .plus = homogeneousUncupRight x y .zero .plus .plus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_4_2 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .plus .plus .minus = homogeneousUncupRight x y .zero .plus .plus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_5_0 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .plus .minus .zero = homogeneousUncupRight x y .zero .plus .minus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_5_1 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .plus .minus .plus = homogeneousUncupRight x y .zero .plus .minus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_5_2 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .plus .minus .minus = homogeneousUncupRight x y .zero .plus .minus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_6_0 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .minus .zero .zero = homogeneousUncupRight x y .zero .minus .zero .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_6_1 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .minus .zero .plus = homogeneousUncupRight x y .zero .minus .zero .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_6_2 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .minus .zero .minus = homogeneousUncupRight x y .zero .minus .zero .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_7_0 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .minus .plus .zero = homogeneousUncupRight x y .zero .minus .plus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_7_1 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .minus .plus .plus = homogeneousUncupRight x y .zero .minus .plus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_7_2 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .minus .plus .minus = homogeneousUncupRight x y .zero .minus .plus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_8_0 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .minus .minus .zero = homogeneousUncupRight x y .zero .minus .minus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_8_1 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .minus .minus .plus = homogeneousUncupRight x y .zero .minus .minus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_8_2 (x y : ℂ) :
    homogeneousUncupLeft x y .zero .minus .minus .minus = homogeneousUncupRight x y .zero .minus .minus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_9_0 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .zero .zero .zero = homogeneousUncupRight x y .plus .zero .zero .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_9_1 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .zero .zero .plus = homogeneousUncupRight x y .plus .zero .zero .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_9_2 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .zero .zero .minus = homogeneousUncupRight x y .plus .zero .zero .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_10_0 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .zero .plus .zero = homogeneousUncupRight x y .plus .zero .plus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_10_1 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .zero .plus .plus = homogeneousUncupRight x y .plus .zero .plus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_10_2 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .zero .plus .minus = homogeneousUncupRight x y .plus .zero .plus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_11_0 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .zero .minus .zero = homogeneousUncupRight x y .plus .zero .minus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_11_1 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .zero .minus .plus = homogeneousUncupRight x y .plus .zero .minus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_11_2 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .zero .minus .minus = homogeneousUncupRight x y .plus .zero .minus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_12_0 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .plus .zero .zero = homogeneousUncupRight x y .plus .plus .zero .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_12_1 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .plus .zero .plus = homogeneousUncupRight x y .plus .plus .zero .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_12_2 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .plus .zero .minus = homogeneousUncupRight x y .plus .plus .zero .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_13_0 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .plus .plus .zero = homogeneousUncupRight x y .plus .plus .plus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_13_1 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .plus .plus .plus = homogeneousUncupRight x y .plus .plus .plus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_13_2 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .plus .plus .minus = homogeneousUncupRight x y .plus .plus .plus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_14_0 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .plus .minus .zero = homogeneousUncupRight x y .plus .plus .minus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_14_1 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .plus .minus .plus = homogeneousUncupRight x y .plus .plus .minus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_14_2 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .plus .minus .minus = homogeneousUncupRight x y .plus .plus .minus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_15_0 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .minus .zero .zero = homogeneousUncupRight x y .plus .minus .zero .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_15_1 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .minus .zero .plus = homogeneousUncupRight x y .plus .minus .zero .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_15_2 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .minus .zero .minus = homogeneousUncupRight x y .plus .minus .zero .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_16_0 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .minus .plus .zero = homogeneousUncupRight x y .plus .minus .plus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_16_1 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .minus .plus .plus = homogeneousUncupRight x y .plus .minus .plus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_16_2 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .minus .plus .minus = homogeneousUncupRight x y .plus .minus .plus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_17_0 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .minus .minus .zero = homogeneousUncupRight x y .plus .minus .minus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_17_1 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .minus .minus .plus = homogeneousUncupRight x y .plus .minus .minus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_17_2 (x y : ℂ) :
    homogeneousUncupLeft x y .plus .minus .minus .minus = homogeneousUncupRight x y .plus .minus .minus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_18_0 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .zero .zero .zero = homogeneousUncupRight x y .minus .zero .zero .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_18_1 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .zero .zero .plus = homogeneousUncupRight x y .minus .zero .zero .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_18_2 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .zero .zero .minus = homogeneousUncupRight x y .minus .zero .zero .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_19_0 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .zero .plus .zero = homogeneousUncupRight x y .minus .zero .plus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_19_1 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .zero .plus .plus = homogeneousUncupRight x y .minus .zero .plus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_19_2 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .zero .plus .minus = homogeneousUncupRight x y .minus .zero .plus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_20_0 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .zero .minus .zero = homogeneousUncupRight x y .minus .zero .minus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_20_1 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .zero .minus .plus = homogeneousUncupRight x y .minus .zero .minus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_20_2 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .zero .minus .minus = homogeneousUncupRight x y .minus .zero .minus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_21_0 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .plus .zero .zero = homogeneousUncupRight x y .minus .plus .zero .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_21_1 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .plus .zero .plus = homogeneousUncupRight x y .minus .plus .zero .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_21_2 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .plus .zero .minus = homogeneousUncupRight x y .minus .plus .zero .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_22_0 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .plus .plus .zero = homogeneousUncupRight x y .minus .plus .plus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_22_1 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .plus .plus .plus = homogeneousUncupRight x y .minus .plus .plus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_22_2 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .plus .plus .minus = homogeneousUncupRight x y .minus .plus .plus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_23_0 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .plus .minus .zero = homogeneousUncupRight x y .minus .plus .minus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_23_1 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .plus .minus .plus = homogeneousUncupRight x y .minus .plus .minus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_23_2 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .plus .minus .minus = homogeneousUncupRight x y .minus .plus .minus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_24_0 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .minus .zero .zero = homogeneousUncupRight x y .minus .minus .zero .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_24_1 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .minus .zero .plus = homogeneousUncupRight x y .minus .minus .zero .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_24_2 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .minus .zero .minus = homogeneousUncupRight x y .minus .minus .zero .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_25_0 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .minus .plus .zero = homogeneousUncupRight x y .minus .minus .plus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_25_1 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .minus .plus .plus = homogeneousUncupRight x y .minus .minus .plus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_25_2 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .minus .plus .minus = homogeneousUncupRight x y .minus .minus .plus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_uncup_entry_26_0 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .minus .minus .zero = homogeneousUncupRight x y .minus .minus .minus .zero := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_26_1 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .minus .minus .plus = homogeneousUncupRight x y .minus .minus .minus .plus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_uncup_entry_26_2 (x y : ℂ) :
    homogeneousUncupLeft x y .minus .minus .minus .minus = homogeneousUncupRight x y .minus .minus .minus .minus := by
  norm_num [homogeneousUncupLeft,homogeneousUncupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_unslide (x y : ℂ) (a b c h : Spin) :
    homogeneousUncupLeft x y a b c h = homogeneousUncupRight x y a b c h := by
  cases a <;> cases b <;> cases c <;> cases h
  · exact homogeneous_uncup_entry_0_0 x y
  · exact homogeneous_uncup_entry_0_1 x y
  · exact homogeneous_uncup_entry_0_2 x y
  · exact homogeneous_uncup_entry_1_0 x y
  · exact homogeneous_uncup_entry_1_1 x y
  · exact homogeneous_uncup_entry_1_2 x y
  · exact homogeneous_uncup_entry_2_0 x y
  · exact homogeneous_uncup_entry_2_1 x y
  · exact homogeneous_uncup_entry_2_2 x y
  · exact homogeneous_uncup_entry_3_0 x y
  · exact homogeneous_uncup_entry_3_1 x y
  · exact homogeneous_uncup_entry_3_2 x y
  · exact homogeneous_uncup_entry_4_0 x y
  · exact homogeneous_uncup_entry_4_1 x y
  · exact homogeneous_uncup_entry_4_2 x y
  · exact homogeneous_uncup_entry_5_0 x y
  · exact homogeneous_uncup_entry_5_1 x y
  · exact homogeneous_uncup_entry_5_2 x y
  · exact homogeneous_uncup_entry_6_0 x y
  · exact homogeneous_uncup_entry_6_1 x y
  · exact homogeneous_uncup_entry_6_2 x y
  · exact homogeneous_uncup_entry_7_0 x y
  · exact homogeneous_uncup_entry_7_1 x y
  · exact homogeneous_uncup_entry_7_2 x y
  · exact homogeneous_uncup_entry_8_0 x y
  · exact homogeneous_uncup_entry_8_1 x y
  · exact homogeneous_uncup_entry_8_2 x y
  · exact homogeneous_uncup_entry_9_0 x y
  · exact homogeneous_uncup_entry_9_1 x y
  · exact homogeneous_uncup_entry_9_2 x y
  · exact homogeneous_uncup_entry_10_0 x y
  · exact homogeneous_uncup_entry_10_1 x y
  · exact homogeneous_uncup_entry_10_2 x y
  · exact homogeneous_uncup_entry_11_0 x y
  · exact homogeneous_uncup_entry_11_1 x y
  · exact homogeneous_uncup_entry_11_2 x y
  · exact homogeneous_uncup_entry_12_0 x y
  · exact homogeneous_uncup_entry_12_1 x y
  · exact homogeneous_uncup_entry_12_2 x y
  · exact homogeneous_uncup_entry_13_0 x y
  · exact homogeneous_uncup_entry_13_1 x y
  · exact homogeneous_uncup_entry_13_2 x y
  · exact homogeneous_uncup_entry_14_0 x y
  · exact homogeneous_uncup_entry_14_1 x y
  · exact homogeneous_uncup_entry_14_2 x y
  · exact homogeneous_uncup_entry_15_0 x y
  · exact homogeneous_uncup_entry_15_1 x y
  · exact homogeneous_uncup_entry_15_2 x y
  · exact homogeneous_uncup_entry_16_0 x y
  · exact homogeneous_uncup_entry_16_1 x y
  · exact homogeneous_uncup_entry_16_2 x y
  · exact homogeneous_uncup_entry_17_0 x y
  · exact homogeneous_uncup_entry_17_1 x y
  · exact homogeneous_uncup_entry_17_2 x y
  · exact homogeneous_uncup_entry_18_0 x y
  · exact homogeneous_uncup_entry_18_1 x y
  · exact homogeneous_uncup_entry_18_2 x y
  · exact homogeneous_uncup_entry_19_0 x y
  · exact homogeneous_uncup_entry_19_1 x y
  · exact homogeneous_uncup_entry_19_2 x y
  · exact homogeneous_uncup_entry_20_0 x y
  · exact homogeneous_uncup_entry_20_1 x y
  · exact homogeneous_uncup_entry_20_2 x y
  · exact homogeneous_uncup_entry_21_0 x y
  · exact homogeneous_uncup_entry_21_1 x y
  · exact homogeneous_uncup_entry_21_2 x y
  · exact homogeneous_uncup_entry_22_0 x y
  · exact homogeneous_uncup_entry_22_1 x y
  · exact homogeneous_uncup_entry_22_2 x y
  · exact homogeneous_uncup_entry_23_0 x y
  · exact homogeneous_uncup_entry_23_1 x y
  · exact homogeneous_uncup_entry_23_2 x y
  · exact homogeneous_uncup_entry_24_0 x y
  · exact homogeneous_uncup_entry_24_1 x y
  · exact homogeneous_uncup_entry_24_2 x y
  · exact homogeneous_uncup_entry_25_0 x y
  · exact homogeneous_uncup_entry_25_1 x y
  · exact homogeneous_uncup_entry_25_2 x y
  · exact homogeneous_uncup_entry_26_0 x y
  · exact homogeneous_uncup_entry_26_1 x y
  · exact homogeneous_uncup_entry_26_2 x y
end PolynomialVacuumAlgebra

end OAI
