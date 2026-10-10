import OAI.Combinatorics.PolynomialVacuum.Algebra.Table
import OAI.Combinatorics.PolynomialVacuum.Algebra.Ring

namespace OAI

namespace PolynomialVacuumAlgebra

noncomputable def baseTwo (x y : ℂ) : Spin → Spin → ℂ
  | .zero,.zero => x+y
  | .plus,.minus => (q^5-q^7)*y
  | .minus,.plus => (q-q^3)*x
  | _,_ => 0

noncomputable def baseThreeFactor (x y z : ℂ) : ℂ := (z+q^2*x)*(z-q^6*y)
noncomputable def baseThree (x y z : ℂ) : Spin → Spin → Spin → ℂ
  | .zero,.zero,.zero => x^2*y+x^2*z+y^2*x+y^2*z+z^2*x+z^2*y+2*(q^2-q^6)*x*y*z
  | .plus,.minus,.zero => (q^5-q^7)*y*baseThreeFactor x y z
  | .minus,.plus,.zero => (q-q^3)*x*baseThreeFactor x y z
  | .zero,.plus,.minus => (q^5-q^7)*z*baseThreeFactor y z x
  | .zero,.minus,.plus => (q-q^3)*y*baseThreeFactor y z x
  | .plus,.zero,.minus => (q^5-q^7)*z*baseThreeFactor z x y
  | .minus,.zero,.plus => (q-q^3)*x*baseThreeFactor z x y
  | _,_,_ => 0

theorem baseTwo_exchange_0 (x y : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.zero,.zero) ab *
      baseTwo x y ab.1 ab.2 ) =
    exchangeDenominator x y * baseTwo y x .zero .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseTwo_rotation_0 (x y : ℂ) :
    zeta ^ charge .zero * baseTwo x y .zero .zero =
    baseTwo y x .zero .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseTwo_cup_0 (x : ℂ) :
    baseTwo x (T*x) .zero .zero =
    (1+T)*x * cup (.zero,.zero) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseTwo_exchange_1 (x y : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.zero,.plus) ab *
      baseTwo x y ab.1 ab.2 ) =
    exchangeDenominator x y * baseTwo y x .zero .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_rotation_1 (x y : ℂ) :
    zeta ^ charge .zero * baseTwo x y .plus .zero =
    baseTwo y x .zero .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_cup_1 (x : ℂ) :
    baseTwo x (T*x) .zero .plus =
    (1+T)*x * cup (.zero,.plus) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_exchange_2 (x y : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.zero,.minus) ab *
      baseTwo x y ab.1 ab.2 ) =
    exchangeDenominator x y * baseTwo y x .zero .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_rotation_2 (x y : ℂ) :
    zeta ^ charge .zero * baseTwo x y .minus .zero =
    baseTwo y x .zero .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_cup_2 (x : ℂ) :
    baseTwo x (T*x) .zero .minus =
    (1+T)*x * cup (.zero,.minus) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_exchange_3 (x y : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.plus,.zero) ab *
      baseTwo x y ab.1 ab.2 ) =
    exchangeDenominator x y * baseTwo y x .plus .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_rotation_3 (x y : ℂ) :
    zeta ^ charge .plus * baseTwo x y .zero .plus =
    baseTwo y x .plus .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_cup_3 (x : ℂ) :
    baseTwo x (T*x) .plus .zero =
    (1+T)*x * cup (.plus,.zero) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_exchange_4 (x y : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.plus,.plus) ab *
      baseTwo x y ab.1 ab.2 ) =
    exchangeDenominator x y * baseTwo y x .plus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_rotation_4 (x y : ℂ) :
    zeta ^ charge .plus * baseTwo x y .plus .plus =
    baseTwo y x .plus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_cup_4 (x : ℂ) :
    baseTwo x (T*x) .plus .plus =
    (1+T)*x * cup (.plus,.plus) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_exchange_5 (x y : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.plus,.minus) ab *
      baseTwo x y ab.1 ab.2 ) =
    exchangeDenominator x y * baseTwo y x .plus .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseTwo_rotation_5 (x y : ℂ) :
    zeta ^ charge .plus * baseTwo x y .minus .plus =
    baseTwo y x .plus .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseTwo_cup_5 (x : ℂ) :
    baseTwo x (T*x) .plus .minus =
    (1+T)*x * cup (.plus,.minus) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseTwo_exchange_6 (x y : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.minus,.zero) ab *
      baseTwo x y ab.1 ab.2 ) =
    exchangeDenominator x y * baseTwo y x .minus .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_rotation_6 (x y : ℂ) :
    zeta ^ charge .minus * baseTwo x y .zero .minus =
    baseTwo y x .minus .zero := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_cup_6 (x : ℂ) :
    baseTwo x (T*x) .minus .zero =
    (1+T)*x * cup (.minus,.zero) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_exchange_7 (x y : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.minus,.plus) ab *
      baseTwo x y ab.1 ab.2 ) =
    exchangeDenominator x y * baseTwo y x .minus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseTwo_rotation_7 (x y : ℂ) :
    zeta ^ charge .minus * baseTwo x y .plus .minus =
    baseTwo y x .minus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseTwo_cup_7 (x : ℂ) :
    baseTwo x (T*x) .minus .plus =
    (1+T)*x * cup (.minus,.plus) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]
  all_goals vacuum_ring_finish

theorem baseTwo_exchange_8 (x y : ℂ) :
    (∑ ab : Pair, exchangeNumerator x y (.minus,.minus) ab *
      baseTwo x y ab.1 ab.2 ) =
    exchangeDenominator x y * baseTwo y x .minus .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_rotation_8 (x y : ℂ) :
    zeta ^ charge .minus * baseTwo x y .minus .minus =
    baseTwo y x .minus .minus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_cup_8 (x : ℂ) :
    baseTwo x (T*x) .minus .minus =
    (1+T)*x * cup (.minus,.minus) := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

theorem baseTwo_exchange (x y : ℂ) (a b : Spin) :
    (∑ ab : Pair, exchangeNumerator x y (a,b) ab * baseTwo x y ab.1 ab.2 ) =
    exchangeDenominator x y * baseTwo y x a b  := by
  cases a <;> cases b
  · exact baseTwo_exchange_0 x y
  · exact baseTwo_exchange_1 x y
  · exact baseTwo_exchange_2 x y
  · exact baseTwo_exchange_3 x y
  · exact baseTwo_exchange_4 x y
  · exact baseTwo_exchange_5 x y
  · exact baseTwo_exchange_6 x y
  · exact baseTwo_exchange_7 x y
  · exact baseTwo_exchange_8 x y

theorem baseTwo_rotation (x y : ℂ) (a b : Spin) :
    zeta ^ charge a * baseTwo x y b a =
    baseTwo y x a b := by
  cases a <;> cases b
  · exact baseTwo_rotation_0 x y
  · exact baseTwo_rotation_1 x y
  · exact baseTwo_rotation_2 x y
  · exact baseTwo_rotation_3 x y
  · exact baseTwo_rotation_4 x y
  · exact baseTwo_rotation_5 x y
  · exact baseTwo_rotation_6 x y
  · exact baseTwo_rotation_7 x y
  · exact baseTwo_rotation_8 x y

theorem baseTwo_cup (x : ℂ) (a b : Spin) :
    baseTwo x (T*x) a b =
    (1+T)*x * cup (a,b) := by
  cases a <;> cases b
  · exact baseTwo_cup_0 x
  · exact baseTwo_cup_1 x
  · exact baseTwo_cup_2 x
  · exact baseTwo_cup_3 x
  · exact baseTwo_cup_4 x
  · exact baseTwo_cup_5 x
  · exact baseTwo_cup_6 x
  · exact baseTwo_cup_7 x
  · exact baseTwo_cup_8 x

end PolynomialVacuumAlgebra

end OAI
