import OAI.Combinatorics.PolynomialVacuum.Algebra.Table
import OAI.Combinatorics.PolynomialVacuum.Algebra.Ring

namespace OAI

namespace PolynomialVacuumAlgebra
noncomputable def homogeneousCupLeft (x y : ℂ) (a b c h : Spin) : ℂ :=
  ∑ i : Spin, ∑ j : Spin, ∑ k : Spin,
    exchangeNumerator x y (a,b) (i,j) *
    exchangeNumerator (T*x) y (j,c) (k,h) * cup (i,k)
noncomputable def homogeneousCupRight (x y : ℂ) (a b c h : Spin) : ℂ :=
  exchangeDenominator x y * exchangeDenominator (T*x) y *
    (if a=h then cup (b,c) else 0)
theorem homogeneous_cup_entry_0_0 (x y : ℂ) :
    homogeneousCupLeft x y .zero .zero .zero .zero = homogeneousCupRight x y .zero .zero .zero .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_0_1 (x y : ℂ) :
    homogeneousCupLeft x y .zero .zero .zero .plus = homogeneousCupRight x y .zero .zero .zero .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_0_2 (x y : ℂ) :
    homogeneousCupLeft x y .zero .zero .zero .minus = homogeneousCupRight x y .zero .zero .zero .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_1_0 (x y : ℂ) :
    homogeneousCupLeft x y .zero .zero .plus .zero = homogeneousCupRight x y .zero .zero .plus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_1_1 (x y : ℂ) :
    homogeneousCupLeft x y .zero .zero .plus .plus = homogeneousCupRight x y .zero .zero .plus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_1_2 (x y : ℂ) :
    homogeneousCupLeft x y .zero .zero .plus .minus = homogeneousCupRight x y .zero .zero .plus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_2_0 (x y : ℂ) :
    homogeneousCupLeft x y .zero .zero .minus .zero = homogeneousCupRight x y .zero .zero .minus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_2_1 (x y : ℂ) :
    homogeneousCupLeft x y .zero .zero .minus .plus = homogeneousCupRight x y .zero .zero .minus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_2_2 (x y : ℂ) :
    homogeneousCupLeft x y .zero .zero .minus .minus = homogeneousCupRight x y .zero .zero .minus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_3_0 (x y : ℂ) :
    homogeneousCupLeft x y .zero .plus .zero .zero = homogeneousCupRight x y .zero .plus .zero .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_3_1 (x y : ℂ) :
    homogeneousCupLeft x y .zero .plus .zero .plus = homogeneousCupRight x y .zero .plus .zero .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_3_2 (x y : ℂ) :
    homogeneousCupLeft x y .zero .plus .zero .minus = homogeneousCupRight x y .zero .plus .zero .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_4_0 (x y : ℂ) :
    homogeneousCupLeft x y .zero .plus .plus .zero = homogeneousCupRight x y .zero .plus .plus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_4_1 (x y : ℂ) :
    homogeneousCupLeft x y .zero .plus .plus .plus = homogeneousCupRight x y .zero .plus .plus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_4_2 (x y : ℂ) :
    homogeneousCupLeft x y .zero .plus .plus .minus = homogeneousCupRight x y .zero .plus .plus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_5_0 (x y : ℂ) :
    homogeneousCupLeft x y .zero .plus .minus .zero = homogeneousCupRight x y .zero .plus .minus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_5_1 (x y : ℂ) :
    homogeneousCupLeft x y .zero .plus .minus .plus = homogeneousCupRight x y .zero .plus .minus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_5_2 (x y : ℂ) :
    homogeneousCupLeft x y .zero .plus .minus .minus = homogeneousCupRight x y .zero .plus .minus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_6_0 (x y : ℂ) :
    homogeneousCupLeft x y .zero .minus .zero .zero = homogeneousCupRight x y .zero .minus .zero .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_6_1 (x y : ℂ) :
    homogeneousCupLeft x y .zero .minus .zero .plus = homogeneousCupRight x y .zero .minus .zero .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_6_2 (x y : ℂ) :
    homogeneousCupLeft x y .zero .minus .zero .minus = homogeneousCupRight x y .zero .minus .zero .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_7_0 (x y : ℂ) :
    homogeneousCupLeft x y .zero .minus .plus .zero = homogeneousCupRight x y .zero .minus .plus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_7_1 (x y : ℂ) :
    homogeneousCupLeft x y .zero .minus .plus .plus = homogeneousCupRight x y .zero .minus .plus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_7_2 (x y : ℂ) :
    homogeneousCupLeft x y .zero .minus .plus .minus = homogeneousCupRight x y .zero .minus .plus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_8_0 (x y : ℂ) :
    homogeneousCupLeft x y .zero .minus .minus .zero = homogeneousCupRight x y .zero .minus .minus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_8_1 (x y : ℂ) :
    homogeneousCupLeft x y .zero .minus .minus .plus = homogeneousCupRight x y .zero .minus .minus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_8_2 (x y : ℂ) :
    homogeneousCupLeft x y .zero .minus .minus .minus = homogeneousCupRight x y .zero .minus .minus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_9_0 (x y : ℂ) :
    homogeneousCupLeft x y .plus .zero .zero .zero = homogeneousCupRight x y .plus .zero .zero .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_9_1 (x y : ℂ) :
    homogeneousCupLeft x y .plus .zero .zero .plus = homogeneousCupRight x y .plus .zero .zero .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_9_2 (x y : ℂ) :
    homogeneousCupLeft x y .plus .zero .zero .minus = homogeneousCupRight x y .plus .zero .zero .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_10_0 (x y : ℂ) :
    homogeneousCupLeft x y .plus .zero .plus .zero = homogeneousCupRight x y .plus .zero .plus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_10_1 (x y : ℂ) :
    homogeneousCupLeft x y .plus .zero .plus .plus = homogeneousCupRight x y .plus .zero .plus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_10_2 (x y : ℂ) :
    homogeneousCupLeft x y .plus .zero .plus .minus = homogeneousCupRight x y .plus .zero .plus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_11_0 (x y : ℂ) :
    homogeneousCupLeft x y .plus .zero .minus .zero = homogeneousCupRight x y .plus .zero .minus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_11_1 (x y : ℂ) :
    homogeneousCupLeft x y .plus .zero .minus .plus = homogeneousCupRight x y .plus .zero .minus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_11_2 (x y : ℂ) :
    homogeneousCupLeft x y .plus .zero .minus .minus = homogeneousCupRight x y .plus .zero .minus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_12_0 (x y : ℂ) :
    homogeneousCupLeft x y .plus .plus .zero .zero = homogeneousCupRight x y .plus .plus .zero .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_12_1 (x y : ℂ) :
    homogeneousCupLeft x y .plus .plus .zero .plus = homogeneousCupRight x y .plus .plus .zero .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_12_2 (x y : ℂ) :
    homogeneousCupLeft x y .plus .plus .zero .minus = homogeneousCupRight x y .plus .plus .zero .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_13_0 (x y : ℂ) :
    homogeneousCupLeft x y .plus .plus .plus .zero = homogeneousCupRight x y .plus .plus .plus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_13_1 (x y : ℂ) :
    homogeneousCupLeft x y .plus .plus .plus .plus = homogeneousCupRight x y .plus .plus .plus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_13_2 (x y : ℂ) :
    homogeneousCupLeft x y .plus .plus .plus .minus = homogeneousCupRight x y .plus .plus .plus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_14_0 (x y : ℂ) :
    homogeneousCupLeft x y .plus .plus .minus .zero = homogeneousCupRight x y .plus .plus .minus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_14_1 (x y : ℂ) :
    homogeneousCupLeft x y .plus .plus .minus .plus = homogeneousCupRight x y .plus .plus .minus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_14_2 (x y : ℂ) :
    homogeneousCupLeft x y .plus .plus .minus .minus = homogeneousCupRight x y .plus .plus .minus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_15_0 (x y : ℂ) :
    homogeneousCupLeft x y .plus .minus .zero .zero = homogeneousCupRight x y .plus .minus .zero .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_15_1 (x y : ℂ) :
    homogeneousCupLeft x y .plus .minus .zero .plus = homogeneousCupRight x y .plus .minus .zero .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_15_2 (x y : ℂ) :
    homogeneousCupLeft x y .plus .minus .zero .minus = homogeneousCupRight x y .plus .minus .zero .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_16_0 (x y : ℂ) :
    homogeneousCupLeft x y .plus .minus .plus .zero = homogeneousCupRight x y .plus .minus .plus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_16_1 (x y : ℂ) :
    homogeneousCupLeft x y .plus .minus .plus .plus = homogeneousCupRight x y .plus .minus .plus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_16_2 (x y : ℂ) :
    homogeneousCupLeft x y .plus .minus .plus .minus = homogeneousCupRight x y .plus .minus .plus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_17_0 (x y : ℂ) :
    homogeneousCupLeft x y .plus .minus .minus .zero = homogeneousCupRight x y .plus .minus .minus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_17_1 (x y : ℂ) :
    homogeneousCupLeft x y .plus .minus .minus .plus = homogeneousCupRight x y .plus .minus .minus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_17_2 (x y : ℂ) :
    homogeneousCupLeft x y .plus .minus .minus .minus = homogeneousCupRight x y .plus .minus .minus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_18_0 (x y : ℂ) :
    homogeneousCupLeft x y .minus .zero .zero .zero = homogeneousCupRight x y .minus .zero .zero .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_18_1 (x y : ℂ) :
    homogeneousCupLeft x y .minus .zero .zero .plus = homogeneousCupRight x y .minus .zero .zero .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_18_2 (x y : ℂ) :
    homogeneousCupLeft x y .minus .zero .zero .minus = homogeneousCupRight x y .minus .zero .zero .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_19_0 (x y : ℂ) :
    homogeneousCupLeft x y .minus .zero .plus .zero = homogeneousCupRight x y .minus .zero .plus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_19_1 (x y : ℂ) :
    homogeneousCupLeft x y .minus .zero .plus .plus = homogeneousCupRight x y .minus .zero .plus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_19_2 (x y : ℂ) :
    homogeneousCupLeft x y .minus .zero .plus .minus = homogeneousCupRight x y .minus .zero .plus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_20_0 (x y : ℂ) :
    homogeneousCupLeft x y .minus .zero .minus .zero = homogeneousCupRight x y .minus .zero .minus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_20_1 (x y : ℂ) :
    homogeneousCupLeft x y .minus .zero .minus .plus = homogeneousCupRight x y .minus .zero .minus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_20_2 (x y : ℂ) :
    homogeneousCupLeft x y .minus .zero .minus .minus = homogeneousCupRight x y .minus .zero .minus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_21_0 (x y : ℂ) :
    homogeneousCupLeft x y .minus .plus .zero .zero = homogeneousCupRight x y .minus .plus .zero .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_21_1 (x y : ℂ) :
    homogeneousCupLeft x y .minus .plus .zero .plus = homogeneousCupRight x y .minus .plus .zero .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_21_2 (x y : ℂ) :
    homogeneousCupLeft x y .minus .plus .zero .minus = homogeneousCupRight x y .minus .plus .zero .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_22_0 (x y : ℂ) :
    homogeneousCupLeft x y .minus .plus .plus .zero = homogeneousCupRight x y .minus .plus .plus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_22_1 (x y : ℂ) :
    homogeneousCupLeft x y .minus .plus .plus .plus = homogeneousCupRight x y .minus .plus .plus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_22_2 (x y : ℂ) :
    homogeneousCupLeft x y .minus .plus .plus .minus = homogeneousCupRight x y .minus .plus .plus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_23_0 (x y : ℂ) :
    homogeneousCupLeft x y .minus .plus .minus .zero = homogeneousCupRight x y .minus .plus .minus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_23_1 (x y : ℂ) :
    homogeneousCupLeft x y .minus .plus .minus .plus = homogeneousCupRight x y .minus .plus .minus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_23_2 (x y : ℂ) :
    homogeneousCupLeft x y .minus .plus .minus .minus = homogeneousCupRight x y .minus .plus .minus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_24_0 (x y : ℂ) :
    homogeneousCupLeft x y .minus .minus .zero .zero = homogeneousCupRight x y .minus .minus .zero .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_24_1 (x y : ℂ) :
    homogeneousCupLeft x y .minus .minus .zero .plus = homogeneousCupRight x y .minus .minus .zero .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_24_2 (x y : ℂ) :
    homogeneousCupLeft x y .minus .minus .zero .minus = homogeneousCupRight x y .minus .minus .zero .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_25_0 (x y : ℂ) :
    homogeneousCupLeft x y .minus .minus .plus .zero = homogeneousCupRight x y .minus .minus .plus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_25_1 (x y : ℂ) :
    homogeneousCupLeft x y .minus .minus .plus .plus = homogeneousCupRight x y .minus .minus .plus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_25_2 (x y : ℂ) :
    homogeneousCupLeft x y .minus .minus .plus .minus = homogeneousCupRight x y .minus .minus .plus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals vacuum_ring_finish
theorem homogeneous_cup_entry_26_0 (x y : ℂ) :
    homogeneousCupLeft x y .minus .minus .minus .zero = homogeneousCupRight x y .minus .minus .minus .zero := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_26_1 (x y : ℂ) :
    homogeneousCupLeft x y .minus .minus .minus .plus = homogeneousCupRight x y .minus .minus .minus .plus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_entry_26_2 (x y : ℂ) :
    homogeneousCupLeft x y .minus .minus .minus .minus = homogeneousCupRight x y .minus .minus .minus .minus := by
  norm_num [homogeneousCupLeft,homogeneousCupRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
theorem homogeneous_cup_slide (x y : ℂ) (a b c h : Spin) :
    homogeneousCupLeft x y a b c h = homogeneousCupRight x y a b c h := by
  cases a <;> cases b <;> cases c <;> cases h
  · exact homogeneous_cup_entry_0_0 x y
  · exact homogeneous_cup_entry_0_1 x y
  · exact homogeneous_cup_entry_0_2 x y
  · exact homogeneous_cup_entry_1_0 x y
  · exact homogeneous_cup_entry_1_1 x y
  · exact homogeneous_cup_entry_1_2 x y
  · exact homogeneous_cup_entry_2_0 x y
  · exact homogeneous_cup_entry_2_1 x y
  · exact homogeneous_cup_entry_2_2 x y
  · exact homogeneous_cup_entry_3_0 x y
  · exact homogeneous_cup_entry_3_1 x y
  · exact homogeneous_cup_entry_3_2 x y
  · exact homogeneous_cup_entry_4_0 x y
  · exact homogeneous_cup_entry_4_1 x y
  · exact homogeneous_cup_entry_4_2 x y
  · exact homogeneous_cup_entry_5_0 x y
  · exact homogeneous_cup_entry_5_1 x y
  · exact homogeneous_cup_entry_5_2 x y
  · exact homogeneous_cup_entry_6_0 x y
  · exact homogeneous_cup_entry_6_1 x y
  · exact homogeneous_cup_entry_6_2 x y
  · exact homogeneous_cup_entry_7_0 x y
  · exact homogeneous_cup_entry_7_1 x y
  · exact homogeneous_cup_entry_7_2 x y
  · exact homogeneous_cup_entry_8_0 x y
  · exact homogeneous_cup_entry_8_1 x y
  · exact homogeneous_cup_entry_8_2 x y
  · exact homogeneous_cup_entry_9_0 x y
  · exact homogeneous_cup_entry_9_1 x y
  · exact homogeneous_cup_entry_9_2 x y
  · exact homogeneous_cup_entry_10_0 x y
  · exact homogeneous_cup_entry_10_1 x y
  · exact homogeneous_cup_entry_10_2 x y
  · exact homogeneous_cup_entry_11_0 x y
  · exact homogeneous_cup_entry_11_1 x y
  · exact homogeneous_cup_entry_11_2 x y
  · exact homogeneous_cup_entry_12_0 x y
  · exact homogeneous_cup_entry_12_1 x y
  · exact homogeneous_cup_entry_12_2 x y
  · exact homogeneous_cup_entry_13_0 x y
  · exact homogeneous_cup_entry_13_1 x y
  · exact homogeneous_cup_entry_13_2 x y
  · exact homogeneous_cup_entry_14_0 x y
  · exact homogeneous_cup_entry_14_1 x y
  · exact homogeneous_cup_entry_14_2 x y
  · exact homogeneous_cup_entry_15_0 x y
  · exact homogeneous_cup_entry_15_1 x y
  · exact homogeneous_cup_entry_15_2 x y
  · exact homogeneous_cup_entry_16_0 x y
  · exact homogeneous_cup_entry_16_1 x y
  · exact homogeneous_cup_entry_16_2 x y
  · exact homogeneous_cup_entry_17_0 x y
  · exact homogeneous_cup_entry_17_1 x y
  · exact homogeneous_cup_entry_17_2 x y
  · exact homogeneous_cup_entry_18_0 x y
  · exact homogeneous_cup_entry_18_1 x y
  · exact homogeneous_cup_entry_18_2 x y
  · exact homogeneous_cup_entry_19_0 x y
  · exact homogeneous_cup_entry_19_1 x y
  · exact homogeneous_cup_entry_19_2 x y
  · exact homogeneous_cup_entry_20_0 x y
  · exact homogeneous_cup_entry_20_1 x y
  · exact homogeneous_cup_entry_20_2 x y
  · exact homogeneous_cup_entry_21_0 x y
  · exact homogeneous_cup_entry_21_1 x y
  · exact homogeneous_cup_entry_21_2 x y
  · exact homogeneous_cup_entry_22_0 x y
  · exact homogeneous_cup_entry_22_1 x y
  · exact homogeneous_cup_entry_22_2 x y
  · exact homogeneous_cup_entry_23_0 x y
  · exact homogeneous_cup_entry_23_1 x y
  · exact homogeneous_cup_entry_23_2 x y
  · exact homogeneous_cup_entry_24_0 x y
  · exact homogeneous_cup_entry_24_1 x y
  · exact homogeneous_cup_entry_24_2 x y
  · exact homogeneous_cup_entry_25_0 x y
  · exact homogeneous_cup_entry_25_1 x y
  · exact homogeneous_cup_entry_25_2 x y
  · exact homogeneous_cup_entry_26_0 x y
  · exact homogeneous_cup_entry_26_1 x y
  · exact homogeneous_cup_entry_26_2 x y
end PolynomialVacuumAlgebra

end OAI
