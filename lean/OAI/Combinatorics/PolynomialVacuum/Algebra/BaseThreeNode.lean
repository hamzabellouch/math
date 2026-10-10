import OAI.Combinatorics.PolynomialVacuum.Algebra.BasePolynomials

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical
theorem baseThree_node_0 (x y : ℂ) :
    baseThree x y (T*x) .zero .zero .zero =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.zero,.zero) ab * cup (.zero,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_node_1 (x y : ℂ) :
    baseThree x y (T*x) .zero .zero .plus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.zero,.plus) ab * cup (.zero,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_2 (x y : ℂ) :
    baseThree x y (T*x) .zero .zero .minus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.zero,.minus) ab * cup (.zero,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_3 (x y : ℂ) :
    baseThree x y (T*x) .zero .plus .zero =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.plus,.zero) ab * cup (.zero,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_4 (x y : ℂ) :
    baseThree x y (T*x) .zero .plus .plus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.plus,.plus) ab * cup (.zero,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_5 (x y : ℂ) :
    baseThree x y (T*x) .zero .plus .minus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.plus,.minus) ab * cup (.zero,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_node_6 (x y : ℂ) :
    baseThree x y (T*x) .zero .minus .zero =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.minus,.zero) ab * cup (.zero,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_7 (x y : ℂ) :
    baseThree x y (T*x) .zero .minus .plus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.minus,.plus) ab * cup (.zero,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_node_8 (x y : ℂ) :
    baseThree x y (T*x) .zero .minus .minus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.minus,.minus) ab * cup (.zero,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_9 (x y : ℂ) :
    baseThree x y (T*x) .plus .zero .zero =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.zero,.zero) ab * cup (.plus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_10 (x y : ℂ) :
    baseThree x y (T*x) .plus .zero .plus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.zero,.plus) ab * cup (.plus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_11 (x y : ℂ) :
    baseThree x y (T*x) .plus .zero .minus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.zero,.minus) ab * cup (.plus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_node_12 (x y : ℂ) :
    baseThree x y (T*x) .plus .plus .zero =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.plus,.zero) ab * cup (.plus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_13 (x y : ℂ) :
    baseThree x y (T*x) .plus .plus .plus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.plus,.plus) ab * cup (.plus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_14 (x y : ℂ) :
    baseThree x y (T*x) .plus .plus .minus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.plus,.minus) ab * cup (.plus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_15 (x y : ℂ) :
    baseThree x y (T*x) .plus .minus .zero =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.minus,.zero) ab * cup (.plus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_node_16 (x y : ℂ) :
    baseThree x y (T*x) .plus .minus .plus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.minus,.plus) ab * cup (.plus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_17 (x y : ℂ) :
    baseThree x y (T*x) .plus .minus .minus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.minus,.minus) ab * cup (.plus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_18 (x y : ℂ) :
    baseThree x y (T*x) .minus .zero .zero =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.zero,.zero) ab * cup (.minus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_19 (x y : ℂ) :
    baseThree x y (T*x) .minus .zero .plus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.zero,.plus) ab * cup (.minus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_node_20 (x y : ℂ) :
    baseThree x y (T*x) .minus .zero .minus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.zero,.minus) ab * cup (.minus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_21 (x y : ℂ) :
    baseThree x y (T*x) .minus .plus .zero =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.plus,.zero) ab * cup (.minus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_node_22 (x y : ℂ) :
    baseThree x y (T*x) .minus .plus .plus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.plus,.plus) ab * cup (.minus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_23 (x y : ℂ) :
    baseThree x y (T*x) .minus .plus .minus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.plus,.minus) ab * cup (.minus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_24 (x y : ℂ) :
    baseThree x y (T*x) .minus .minus .zero =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.minus,.zero) ab * cup (.minus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_25 (x y : ℂ) :
    baseThree x y (T*x) .minus .minus .plus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.minus,.plus) ab * cup (.minus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node_26 (x y : ℂ) :
    baseThree x y (T*x) .minus .minus .minus =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (.minus,.minus) ab * cup (.minus,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_node (x y : ℂ) (a b c : Spin) :
    baseThree x y (T*x) a b c =
      (1+T)*x*(∑ ab : Pair, exchangeNumerator (T*x) y (b,c) ab * cup (a,ab.1) * (if ab.2=Spin.zero then 1 else 0)) := by
  cases a <;> cases b <;> cases c
  · exact baseThree_node_0 x y
  · exact baseThree_node_1 x y
  · exact baseThree_node_2 x y
  · exact baseThree_node_3 x y
  · exact baseThree_node_4 x y
  · exact baseThree_node_5 x y
  · exact baseThree_node_6 x y
  · exact baseThree_node_7 x y
  · exact baseThree_node_8 x y
  · exact baseThree_node_9 x y
  · exact baseThree_node_10 x y
  · exact baseThree_node_11 x y
  · exact baseThree_node_12 x y
  · exact baseThree_node_13 x y
  · exact baseThree_node_14 x y
  · exact baseThree_node_15 x y
  · exact baseThree_node_16 x y
  · exact baseThree_node_17 x y
  · exact baseThree_node_18 x y
  · exact baseThree_node_19 x y
  · exact baseThree_node_20 x y
  · exact baseThree_node_21 x y
  · exact baseThree_node_22 x y
  · exact baseThree_node_23 x y
  · exact baseThree_node_24 x y
  · exact baseThree_node_25 x y
  · exact baseThree_node_26 x y
end PolynomialVacuumAlgebra

end OAI
