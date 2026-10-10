import OAI.Combinatorics.PolynomialVacuum.Algebra.Ring
import OAI.Combinatorics.PolynomialVacuum.Algebra.BaseTwo

namespace OAI

namespace PolynomialVacuumAlgebra

theorem baseThree_exchange_0 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.zero,.zero) ab *
      baseThree x y z ab.1 ab.2 .zero) =
    exchangeDenominator x y * baseThree y x z .zero .zero .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_rotation_0 (x y z : ℂ) :
    zeta ^ charge .zero * baseThree x y z .zero .zero .zero =
    baseThree z x y .zero .zero .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_cup_0 (x z : ℂ) :
    baseThree x (T*x) z .zero .zero .zero =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.zero,.zero) * (if .zero = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_exchange_1 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.zero,.zero) ab *
      baseThree x y z ab.1 ab.2 .plus) =
    exchangeDenominator x y * baseThree y x z .zero .zero .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_1 (x y z : ℂ) :
    zeta ^ charge .zero * baseThree x y z .zero .plus .zero =
    baseThree z x y .zero .zero .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_1 (x z : ℂ) :
    baseThree x (T*x) z .zero .zero .plus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.zero,.zero) * (if .plus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_2 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.zero,.zero) ab *
      baseThree x y z ab.1 ab.2 .minus) =
    exchangeDenominator x y * baseThree y x z .zero .zero .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_2 (x y z : ℂ) :
    zeta ^ charge .zero * baseThree x y z .zero .minus .zero =
    baseThree z x y .zero .zero .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_2 (x z : ℂ) :
    baseThree x (T*x) z .zero .zero .minus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.zero,.zero) * (if .minus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_3 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.zero,.plus) ab *
      baseThree x y z ab.1 ab.2 .zero) =
    exchangeDenominator x y * baseThree y x z .zero .plus .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_3 (x y z : ℂ) :
    zeta ^ charge .zero * baseThree x y z .plus .zero .zero =
    baseThree z x y .zero .plus .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_3 (x z : ℂ) :
    baseThree x (T*x) z .zero .plus .zero =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.zero,.plus) * (if .zero = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_4 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.zero,.plus) ab *
      baseThree x y z ab.1 ab.2 .plus) =
    exchangeDenominator x y * baseThree y x z .zero .plus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_4 (x y z : ℂ) :
    zeta ^ charge .zero * baseThree x y z .plus .plus .zero =
    baseThree z x y .zero .plus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_4 (x z : ℂ) :
    baseThree x (T*x) z .zero .plus .plus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.zero,.plus) * (if .plus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_5 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.zero,.plus) ab *
      baseThree x y z ab.1 ab.2 .minus) =
    exchangeDenominator x y * baseThree y x z .zero .plus .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_rotation_5 (x y z : ℂ) :
    zeta ^ charge .zero * baseThree x y z .plus .minus .zero =
    baseThree z x y .zero .plus .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_5 (x z : ℂ) :
    baseThree x (T*x) z .zero .plus .minus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.zero,.plus) * (if .minus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_exchange_6 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.zero,.minus) ab *
      baseThree x y z ab.1 ab.2 .zero) =
    exchangeDenominator x y * baseThree y x z .zero .minus .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_6 (x y z : ℂ) :
    zeta ^ charge .zero * baseThree x y z .minus .zero .zero =
    baseThree z x y .zero .minus .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_6 (x z : ℂ) :
    baseThree x (T*x) z .zero .minus .zero =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.zero,.minus) * (if .zero = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_7 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.zero,.minus) ab *
      baseThree x y z ab.1 ab.2 .plus) =
    exchangeDenominator x y * baseThree y x z .zero .minus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_rotation_7 (x y z : ℂ) :
    zeta ^ charge .zero * baseThree x y z .minus .plus .zero =
    baseThree z x y .zero .minus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_7 (x z : ℂ) :
    baseThree x (T*x) z .zero .minus .plus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.zero,.minus) * (if .plus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_exchange_8 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.zero,.minus) ab *
      baseThree x y z ab.1 ab.2 .minus) =
    exchangeDenominator x y * baseThree y x z .zero .minus .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_8 (x y z : ℂ) :
    zeta ^ charge .zero * baseThree x y z .minus .minus .zero =
    baseThree z x y .zero .minus .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_8 (x z : ℂ) :
    baseThree x (T*x) z .zero .minus .minus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.zero,.minus) * (if .minus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_9 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.plus,.zero) ab *
      baseThree x y z ab.1 ab.2 .zero) =
    exchangeDenominator x y * baseThree y x z .plus .zero .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_9 (x y z : ℂ) :
    zeta ^ charge .plus * baseThree x y z .zero .zero .plus =
    baseThree z x y .plus .zero .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_9 (x z : ℂ) :
    baseThree x (T*x) z .plus .zero .zero =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.plus,.zero) * (if .zero = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_10 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.plus,.zero) ab *
      baseThree x y z ab.1 ab.2 .plus) =
    exchangeDenominator x y * baseThree y x z .plus .zero .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_10 (x y z : ℂ) :
    zeta ^ charge .plus * baseThree x y z .zero .plus .plus =
    baseThree z x y .plus .zero .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_10 (x z : ℂ) :
    baseThree x (T*x) z .plus .zero .plus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.plus,.zero) * (if .plus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_11 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.plus,.zero) ab *
      baseThree x y z ab.1 ab.2 .minus) =
    exchangeDenominator x y * baseThree y x z .plus .zero .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_rotation_11 (x y z : ℂ) :
    zeta ^ charge .plus * baseThree x y z .zero .minus .plus =
    baseThree z x y .plus .zero .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_cup_11 (x z : ℂ) :
    baseThree x (T*x) z .plus .zero .minus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.plus,.zero) * (if .minus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_exchange_12 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.plus,.plus) ab *
      baseThree x y z ab.1 ab.2 .zero) =
    exchangeDenominator x y * baseThree y x z .plus .plus .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_12 (x y z : ℂ) :
    zeta ^ charge .plus * baseThree x y z .plus .zero .plus =
    baseThree z x y .plus .plus .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_12 (x z : ℂ) :
    baseThree x (T*x) z .plus .plus .zero =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.plus,.plus) * (if .zero = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_13 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.plus,.plus) ab *
      baseThree x y z ab.1 ab.2 .plus) =
    exchangeDenominator x y * baseThree y x z .plus .plus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_13 (x y z : ℂ) :
    zeta ^ charge .plus * baseThree x y z .plus .plus .plus =
    baseThree z x y .plus .plus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_13 (x z : ℂ) :
    baseThree x (T*x) z .plus .plus .plus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.plus,.plus) * (if .plus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_14 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.plus,.plus) ab *
      baseThree x y z ab.1 ab.2 .minus) =
    exchangeDenominator x y * baseThree y x z .plus .plus .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_14 (x y z : ℂ) :
    zeta ^ charge .plus * baseThree x y z .plus .minus .plus =
    baseThree z x y .plus .plus .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_14 (x z : ℂ) :
    baseThree x (T*x) z .plus .plus .minus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.plus,.plus) * (if .minus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_15 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.plus,.minus) ab *
      baseThree x y z ab.1 ab.2 .zero) =
    exchangeDenominator x y * baseThree y x z .plus .minus .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_rotation_15 (x y z : ℂ) :
    zeta ^ charge .plus * baseThree x y z .minus .zero .plus =
    baseThree z x y .plus .minus .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_cup_15 (x z : ℂ) :
    baseThree x (T*x) z .plus .minus .zero =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.plus,.minus) * (if .zero = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_exchange_16 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.plus,.minus) ab *
      baseThree x y z ab.1 ab.2 .plus) =
    exchangeDenominator x y * baseThree y x z .plus .minus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_16 (x y z : ℂ) :
    zeta ^ charge .plus * baseThree x y z .minus .plus .plus =
    baseThree z x y .plus .minus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_16 (x z : ℂ) :
    baseThree x (T*x) z .plus .minus .plus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.plus,.minus) * (if .plus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_17 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.plus,.minus) ab *
      baseThree x y z ab.1 ab.2 .minus) =
    exchangeDenominator x y * baseThree y x z .plus .minus .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_17 (x y z : ℂ) :
    zeta ^ charge .plus * baseThree x y z .minus .minus .plus =
    baseThree z x y .plus .minus .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_17 (x z : ℂ) :
    baseThree x (T*x) z .plus .minus .minus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.plus,.minus) * (if .minus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_18 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.minus,.zero) ab *
      baseThree x y z ab.1 ab.2 .zero) =
    exchangeDenominator x y * baseThree y x z .minus .zero .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_18 (x y z : ℂ) :
    zeta ^ charge .minus * baseThree x y z .zero .zero .minus =
    baseThree z x y .minus .zero .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_18 (x z : ℂ) :
    baseThree x (T*x) z .minus .zero .zero =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.minus,.zero) * (if .zero = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_19 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.minus,.zero) ab *
      baseThree x y z ab.1 ab.2 .plus) =
    exchangeDenominator x y * baseThree y x z .minus .zero .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_rotation_19 (x y z : ℂ) :
    zeta ^ charge .minus * baseThree x y z .zero .plus .minus =
    baseThree z x y .minus .zero .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_cup_19 (x z : ℂ) :
    baseThree x (T*x) z .minus .zero .plus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.minus,.zero) * (if .plus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_exchange_20 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.minus,.zero) ab *
      baseThree x y z ab.1 ab.2 .minus) =
    exchangeDenominator x y * baseThree y x z .minus .zero .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_20 (x y z : ℂ) :
    zeta ^ charge .minus * baseThree x y z .zero .minus .minus =
    baseThree z x y .minus .zero .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_20 (x z : ℂ) :
    baseThree x (T*x) z .minus .zero .minus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.minus,.zero) * (if .minus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_21 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.minus,.plus) ab *
      baseThree x y z ab.1 ab.2 .zero) =
    exchangeDenominator x y * baseThree y x z .minus .plus .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_rotation_21 (x y z : ℂ) :
    zeta ^ charge .minus * baseThree x y z .plus .zero .minus =
    baseThree z x y .minus .plus .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_cup_21 (x z : ℂ) :
    baseThree x (T*x) z .minus .plus .zero =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.minus,.plus) * (if .zero = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseThree_exchange_22 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.minus,.plus) ab *
      baseThree x y z ab.1 ab.2 .plus) =
    exchangeDenominator x y * baseThree y x z .minus .plus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_22 (x y z : ℂ) :
    zeta ^ charge .minus * baseThree x y z .plus .plus .minus =
    baseThree z x y .minus .plus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_22 (x z : ℂ) :
    baseThree x (T*x) z .minus .plus .plus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.minus,.plus) * (if .plus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_23 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.minus,.plus) ab *
      baseThree x y z ab.1 ab.2 .minus) =
    exchangeDenominator x y * baseThree y x z .minus .plus .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_23 (x y z : ℂ) :
    zeta ^ charge .minus * baseThree x y z .plus .minus .minus =
    baseThree z x y .minus .plus .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_23 (x z : ℂ) :
    baseThree x (T*x) z .minus .plus .minus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.minus,.plus) * (if .minus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_24 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.minus,.minus) ab *
      baseThree x y z ab.1 ab.2 .zero) =
    exchangeDenominator x y * baseThree y x z .minus .minus .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_24 (x y z : ℂ) :
    zeta ^ charge .minus * baseThree x y z .minus .zero .minus =
    baseThree z x y .minus .minus .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_24 (x z : ℂ) :
    baseThree x (T*x) z .minus .minus .zero =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.minus,.minus) * (if .zero = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_25 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.minus,.minus) ab *
      baseThree x y z ab.1 ab.2 .plus) =
    exchangeDenominator x y * baseThree y x z .minus .minus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_25 (x y z : ℂ) :
    zeta ^ charge .minus * baseThree x y z .minus .plus .minus =
    baseThree z x y .minus .minus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_25 (x z : ℂ) :
    baseThree x (T*x) z .minus .minus .plus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.minus,.minus) * (if .plus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange_26 (x y z : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.minus,.minus) ab *
      baseThree x y z ab.1 ab.2 .minus) =
    exchangeDenominator x y * baseThree y x z .minus .minus .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_rotation_26 (x y z : ℂ) :
    zeta ^ charge .minus * baseThree x y z .minus .minus .minus =
    baseThree z x y .minus .minus .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_cup_26 (x z : ℂ) :
    baseThree x (T*x) z .minus .minus .minus =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (.minus,.minus) * (if .minus = Spin.zero then 1 else 0) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseThree_exchange (x y z : ℂ) (a b c : Spin) :
    (∑ ab : Pair, exchangeNumerator x y (a,b) ab * baseThree x y z ab.1 ab.2 c) =
    exchangeDenominator x y * baseThree y x z a b c := by
  cases a <;> cases b <;> cases c
  · exact baseThree_exchange_0 x y z
  · exact baseThree_exchange_1 x y z
  · exact baseThree_exchange_2 x y z
  · exact baseThree_exchange_3 x y z
  · exact baseThree_exchange_4 x y z
  · exact baseThree_exchange_5 x y z
  · exact baseThree_exchange_6 x y z
  · exact baseThree_exchange_7 x y z
  · exact baseThree_exchange_8 x y z
  · exact baseThree_exchange_9 x y z
  · exact baseThree_exchange_10 x y z
  · exact baseThree_exchange_11 x y z
  · exact baseThree_exchange_12 x y z
  · exact baseThree_exchange_13 x y z
  · exact baseThree_exchange_14 x y z
  · exact baseThree_exchange_15 x y z
  · exact baseThree_exchange_16 x y z
  · exact baseThree_exchange_17 x y z
  · exact baseThree_exchange_18 x y z
  · exact baseThree_exchange_19 x y z
  · exact baseThree_exchange_20 x y z
  · exact baseThree_exchange_21 x y z
  · exact baseThree_exchange_22 x y z
  · exact baseThree_exchange_23 x y z
  · exact baseThree_exchange_24 x y z
  · exact baseThree_exchange_25 x y z
  · exact baseThree_exchange_26 x y z

theorem baseThree_rotation (x y z : ℂ) (a b c : Spin) :
    zeta ^ charge a * baseThree x y z b c a =
    baseThree z x y a b c := by
  cases a <;> cases b <;> cases c
  · exact baseThree_rotation_0 x y z
  · exact baseThree_rotation_1 x y z
  · exact baseThree_rotation_2 x y z
  · exact baseThree_rotation_3 x y z
  · exact baseThree_rotation_4 x y z
  · exact baseThree_rotation_5 x y z
  · exact baseThree_rotation_6 x y z
  · exact baseThree_rotation_7 x y z
  · exact baseThree_rotation_8 x y z
  · exact baseThree_rotation_9 x y z
  · exact baseThree_rotation_10 x y z
  · exact baseThree_rotation_11 x y z
  · exact baseThree_rotation_12 x y z
  · exact baseThree_rotation_13 x y z
  · exact baseThree_rotation_14 x y z
  · exact baseThree_rotation_15 x y z
  · exact baseThree_rotation_16 x y z
  · exact baseThree_rotation_17 x y z
  · exact baseThree_rotation_18 x y z
  · exact baseThree_rotation_19 x y z
  · exact baseThree_rotation_20 x y z
  · exact baseThree_rotation_21 x y z
  · exact baseThree_rotation_22 x y z
  · exact baseThree_rotation_23 x y z
  · exact baseThree_rotation_24 x y z
  · exact baseThree_rotation_25 x y z
  · exact baseThree_rotation_26 x y z

theorem baseThree_cup (x z : ℂ) (a b c : Spin) :
    baseThree x (T*x) z a b c =
    (1+T)*x * (z-t^5*x)*(z-t^6*x) * cup (a,b) * (if c = Spin.zero then 1 else 0) := by
  cases a <;> cases b <;> cases c
  · exact baseThree_cup_0 x z
  · exact baseThree_cup_1 x z
  · exact baseThree_cup_2 x z
  · exact baseThree_cup_3 x z
  · exact baseThree_cup_4 x z
  · exact baseThree_cup_5 x z
  · exact baseThree_cup_6 x z
  · exact baseThree_cup_7 x z
  · exact baseThree_cup_8 x z
  · exact baseThree_cup_9 x z
  · exact baseThree_cup_10 x z
  · exact baseThree_cup_11 x z
  · exact baseThree_cup_12 x z
  · exact baseThree_cup_13 x z
  · exact baseThree_cup_14 x z
  · exact baseThree_cup_15 x z
  · exact baseThree_cup_16 x z
  · exact baseThree_cup_17 x z
  · exact baseThree_cup_18 x z
  · exact baseThree_cup_19 x z
  · exact baseThree_cup_20 x z
  · exact baseThree_cup_21 x z
  · exact baseThree_cup_22 x z
  · exact baseThree_cup_23 x z
  · exact baseThree_cup_24 x z
  · exact baseThree_cup_25 x z
  · exact baseThree_cup_26 x z

end PolynomialVacuumAlgebra

end OAI
