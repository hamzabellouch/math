import OAI.Combinatorics.PolynomialVacuum.Algebra.PolynomialScalars

namespace OAI

namespace PolynomialVacuumAlgebra

noncomputable def exchangeTable (x y : ℂ) : Pair → Pair → ℂ
  | (.zero,.zero), (.zero,.zero) => -q^2*x^2-q^4*x*y-q^6*x*y+y^2
  | (.zero,.zero), (.plus,.minus) => -q*x^2-q^5*x^2+q*x*y+q^5*x*y
  | (.zero,.zero), (.minus,.plus) => -q*x*y+q^5*x*y+q*y^2-q^5*y^2
  | (.zero,.plus), (.zero,.plus) => x*y-q^4*x*y-q^2*y^2-q^6*y^2
  | (.zero,.plus), (.plus,.zero) => -q^2*x^2-x*y+q^2*x*y+y^2
  | (.zero,.minus), (.zero,.minus) => x^2-q^4*x^2-q^2*x*y-q^6*x*y
  | (.zero,.minus), (.minus,.zero) => -q^2*x^2-x*y+q^2*x*y+y^2
  | (.plus,.zero), (.zero,.plus) => -q^2*x^2-x*y+q^2*x*y+y^2
  | (.plus,.zero), (.plus,.zero) => x^2-q^4*x^2-q^2*x*y-q^6*x*y
  | (.plus,.plus), (.plus,.plus) => x^2-q^4*x*y-q^6*x*y-q^2*y^2
  | (.plus,.minus), (.zero,.zero) => -q*x^2-q^5*x^2+q*x*y+q^5*x*y
  | (.plus,.minus), (.plus,.minus) => x^2+q^2*x^2-q^4*x^2-q^6*x^2-2*q^2*x*y
  | (.plus,.minus), (.minus,.plus) => q^4*x^2-q^4*x*y-q^6*x*y+q^6*y^2
  | (.minus,.zero), (.zero,.minus) => -q^2*x^2-x*y+q^2*x*y+y^2
  | (.minus,.zero), (.minus,.zero) => x*y-q^4*x*y-q^2*y^2-q^6*y^2
  | (.minus,.plus), (.zero,.zero) => -q*x*y+q^5*x*y+q*y^2-q^5*y^2
  | (.minus,.plus), (.plus,.minus) => q^4*x^2-q^4*x*y-q^6*x*y+q^6*y^2
  | (.minus,.plus), (.minus,.plus) => 2*x*y-y^2-q^2*y^2-q^4*y^2-q^6*y^2
  | (.minus,.minus), (.minus,.minus) => x^2-q^4*x*y-q^6*x*y-q^2*y^2
  | _, _ => 0

theorem numerator_entry_0_0 (x y : ℂ) :
    exchangeNumerator x y (.zero,.zero) (.zero,.zero) = -q^2*x^2-q^4*x*y-q^6*x*y+y^2 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_eight,q_pow_10,q_pow_12]
  ring

theorem numerator_entry_0_1 (x y : ℂ) :
    exchangeNumerator x y (.zero,.zero) (.zero,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_0_2 (x y : ℂ) :
    exchangeNumerator x y (.zero,.zero) (.zero,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_0_3 (x y : ℂ) :
    exchangeNumerator x y (.zero,.zero) (.plus,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_0_4 (x y : ℂ) :
    exchangeNumerator x y (.zero,.zero) (.plus,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_0_5 (x y : ℂ) :
    exchangeNumerator x y (.zero,.zero) (.plus,.minus) = -q*x^2-q^5*x^2+q*x*y+q^5*x*y := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17,q_pow_19,q_pow_21,q_pow_23,q_pow_25,q_pow_27]
  ring

theorem numerator_entry_0_6 (x y : ℂ) :
    exchangeNumerator x y (.zero,.zero) (.minus,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_0_7 (x y : ℂ) :
    exchangeNumerator x y (.zero,.zero) (.minus,.plus) = -q*x*y+q^5*x*y+q*y^2-q^5*y^2 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_9,q_pow_11,q_pow_15,q_pow_17,q_pow_19,q_pow_21,q_pow_23,q_pow_25,q_pow_27]
  ring

theorem numerator_entry_0_8 (x y : ℂ) :
    exchangeNumerator x y (.zero,.zero) (.minus,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_1_0 (x y : ℂ) :
    exchangeNumerator x y (.zero,.plus) (.zero,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_1_1 (x y : ℂ) :
    exchangeNumerator x y (.zero,.plus) (.zero,.plus) = x*y-q^4*x*y-q^2*y^2-q^6*y^2 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_10,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_24,q_pow_26,q_pow_28,q_pow_30,q_pow_32,q_pow_34,q_pow_36,q_pow_38,q_pow_40,q_pow_42,q_pow_44]
  ring

theorem numerator_entry_1_2 (x y : ℂ) :
    exchangeNumerator x y (.zero,.plus) (.zero,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_1_3 (x y : ℂ) :
    exchangeNumerator x y (.zero,.plus) (.plus,.zero) = -q^2*x^2-x*y+q^2*x*y+y^2 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_24,q_pow_26,q_pow_28,q_pow_30,q_pow_32,q_pow_34,q_pow_36,q_pow_38]
  ring

theorem numerator_entry_1_4 (x y : ℂ) :
    exchangeNumerator x y (.zero,.plus) (.plus,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_1_5 (x y : ℂ) :
    exchangeNumerator x y (.zero,.plus) (.plus,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_1_6 (x y : ℂ) :
    exchangeNumerator x y (.zero,.plus) (.minus,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_1_7 (x y : ℂ) :
    exchangeNumerator x y (.zero,.plus) (.minus,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_1_8 (x y : ℂ) :
    exchangeNumerator x y (.zero,.plus) (.minus,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_2_0 (x y : ℂ) :
    exchangeNumerator x y (.zero,.minus) (.zero,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_2_1 (x y : ℂ) :
    exchangeNumerator x y (.zero,.minus) (.zero,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_2_2 (x y : ℂ) :
    exchangeNumerator x y (.zero,.minus) (.zero,.minus) = x^2-q^4*x^2-q^2*x*y-q^6*x*y := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_24,q_pow_26,q_pow_28,q_pow_30,q_pow_32]
  ring

theorem numerator_entry_2_3 (x y : ℂ) :
    exchangeNumerator x y (.zero,.minus) (.plus,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_2_4 (x y : ℂ) :
    exchangeNumerator x y (.zero,.minus) (.plus,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_2_5 (x y : ℂ) :
    exchangeNumerator x y (.zero,.minus) (.plus,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_2_6 (x y : ℂ) :
    exchangeNumerator x y (.zero,.minus) (.minus,.zero) = -q^2*x^2-x*y+q^2*x*y+y^2 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_24,q_pow_26,q_pow_28,q_pow_30,q_pow_32,q_pow_34,q_pow_36,q_pow_38]
  ring

theorem numerator_entry_2_7 (x y : ℂ) :
    exchangeNumerator x y (.zero,.minus) (.minus,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_2_8 (x y : ℂ) :
    exchangeNumerator x y (.zero,.minus) (.minus,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_3_0 (x y : ℂ) :
    exchangeNumerator x y (.plus,.zero) (.zero,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_3_1 (x y : ℂ) :
    exchangeNumerator x y (.plus,.zero) (.zero,.plus) = -q^2*x^2-x*y+q^2*x*y+y^2 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_24,q_pow_26,q_pow_28,q_pow_30,q_pow_32,q_pow_34,q_pow_36,q_pow_38]
  ring

theorem numerator_entry_3_2 (x y : ℂ) :
    exchangeNumerator x y (.plus,.zero) (.zero,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_3_3 (x y : ℂ) :
    exchangeNumerator x y (.plus,.zero) (.plus,.zero) = x^2-q^4*x^2-q^2*x*y-q^6*x*y := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_24,q_pow_26,q_pow_28,q_pow_30,q_pow_32]
  ring

theorem numerator_entry_3_4 (x y : ℂ) :
    exchangeNumerator x y (.plus,.zero) (.plus,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_3_5 (x y : ℂ) :
    exchangeNumerator x y (.plus,.zero) (.plus,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_3_6 (x y : ℂ) :
    exchangeNumerator x y (.plus,.zero) (.minus,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_3_7 (x y : ℂ) :
    exchangeNumerator x y (.plus,.zero) (.minus,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_3_8 (x y : ℂ) :
    exchangeNumerator x y (.plus,.zero) (.minus,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_4_0 (x y : ℂ) :
    exchangeNumerator x y (.plus,.plus) (.zero,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_4_1 (x y : ℂ) :
    exchangeNumerator x y (.plus,.plus) (.zero,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_4_2 (x y : ℂ) :
    exchangeNumerator x y (.plus,.plus) (.zero,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_4_3 (x y : ℂ) :
    exchangeNumerator x y (.plus,.plus) (.plus,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_4_4 (x y : ℂ) :
    exchangeNumerator x y (.plus,.plus) (.plus,.plus) = x^2-q^4*x*y-q^6*x*y-q^2*y^2 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_10]
  ring

theorem numerator_entry_4_5 (x y : ℂ) :
    exchangeNumerator x y (.plus,.plus) (.plus,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_4_6 (x y : ℂ) :
    exchangeNumerator x y (.plus,.plus) (.minus,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_4_7 (x y : ℂ) :
    exchangeNumerator x y (.plus,.plus) (.minus,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_4_8 (x y : ℂ) :
    exchangeNumerator x y (.plus,.plus) (.minus,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_5_0 (x y : ℂ) :
    exchangeNumerator x y (.plus,.minus) (.zero,.zero) = -q*x^2-q^5*x^2+q*x*y+q^5*x*y := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17,q_pow_19,q_pow_21,q_pow_23,q_pow_25,q_pow_27]
  ring

theorem numerator_entry_5_1 (x y : ℂ) :
    exchangeNumerator x y (.plus,.minus) (.zero,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_5_2 (x y : ℂ) :
    exchangeNumerator x y (.plus,.minus) (.zero,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_5_3 (x y : ℂ) :
    exchangeNumerator x y (.plus,.minus) (.plus,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_5_4 (x y : ℂ) :
    exchangeNumerator x y (.plus,.minus) (.plus,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_5_5 (x y : ℂ) :
    exchangeNumerator x y (.plus,.minus) (.plus,.minus) = x^2+q^2*x^2-q^4*x^2-q^6*x^2-2*q^2*x*y := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_24,q_pow_26,q_pow_28,q_pow_30,q_pow_32,q_pow_34,q_pow_36,q_pow_38]
  ring

theorem numerator_entry_5_6 (x y : ℂ) :
    exchangeNumerator x y (.plus,.minus) (.minus,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_5_7 (x y : ℂ) :
    exchangeNumerator x y (.plus,.minus) (.minus,.plus) = q^4*x^2-q^4*x*y-q^6*x*y+q^6*y^2 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_24,q_pow_26,q_pow_28,q_pow_30,q_pow_32,q_pow_34,q_pow_36,q_pow_38]
  ring

theorem numerator_entry_5_8 (x y : ℂ) :
    exchangeNumerator x y (.plus,.minus) (.minus,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_6_0 (x y : ℂ) :
    exchangeNumerator x y (.minus,.zero) (.zero,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_6_1 (x y : ℂ) :
    exchangeNumerator x y (.minus,.zero) (.zero,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_6_2 (x y : ℂ) :
    exchangeNumerator x y (.minus,.zero) (.zero,.minus) = -q^2*x^2-x*y+q^2*x*y+y^2 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_24,q_pow_26,q_pow_28,q_pow_30,q_pow_32,q_pow_34,q_pow_36,q_pow_38]
  ring

theorem numerator_entry_6_3 (x y : ℂ) :
    exchangeNumerator x y (.minus,.zero) (.plus,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_6_4 (x y : ℂ) :
    exchangeNumerator x y (.minus,.zero) (.plus,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_6_5 (x y : ℂ) :
    exchangeNumerator x y (.minus,.zero) (.plus,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_6_6 (x y : ℂ) :
    exchangeNumerator x y (.minus,.zero) (.minus,.zero) = x*y-q^4*x*y-q^2*y^2-q^6*y^2 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_10,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_24,q_pow_26,q_pow_28,q_pow_30,q_pow_32,q_pow_34,q_pow_36,q_pow_38,q_pow_40,q_pow_42,q_pow_44]
  ring

theorem numerator_entry_6_7 (x y : ℂ) :
    exchangeNumerator x y (.minus,.zero) (.minus,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_6_8 (x y : ℂ) :
    exchangeNumerator x y (.minus,.zero) (.minus,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_7_0 (x y : ℂ) :
    exchangeNumerator x y (.minus,.plus) (.zero,.zero) = -q*x*y+q^5*x*y+q*y^2-q^5*y^2 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_9,q_pow_11,q_pow_15,q_pow_17,q_pow_19,q_pow_21,q_pow_23,q_pow_25,q_pow_27]
  ring

theorem numerator_entry_7_1 (x y : ℂ) :
    exchangeNumerator x y (.minus,.plus) (.zero,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_7_2 (x y : ℂ) :
    exchangeNumerator x y (.minus,.plus) (.zero,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_7_3 (x y : ℂ) :
    exchangeNumerator x y (.minus,.plus) (.plus,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_7_4 (x y : ℂ) :
    exchangeNumerator x y (.minus,.plus) (.plus,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_7_5 (x y : ℂ) :
    exchangeNumerator x y (.minus,.plus) (.plus,.minus) = q^4*x^2-q^4*x*y-q^6*x*y+q^6*y^2 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_24,q_pow_26,q_pow_28,q_pow_30,q_pow_32,q_pow_34,q_pow_36,q_pow_38]
  ring

theorem numerator_entry_7_6 (x y : ℂ) :
    exchangeNumerator x y (.minus,.plus) (.minus,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_7_7 (x y : ℂ) :
    exchangeNumerator x y (.minus,.plus) (.minus,.plus) = 2*x*y-y^2-q^2*y^2-q^4*y^2-q^6*y^2 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_24,q_pow_26,q_pow_28,q_pow_30,q_pow_32,q_pow_34,q_pow_36,q_pow_38]
  ring

theorem numerator_entry_7_8 (x y : ℂ) :
    exchangeNumerator x y (.minus,.plus) (.minus,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_8_0 (x y : ℂ) :
    exchangeNumerator x y (.minus,.minus) (.zero,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_8_1 (x y : ℂ) :
    exchangeNumerator x y (.minus,.minus) (.zero,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_8_2 (x y : ℂ) :
    exchangeNumerator x y (.minus,.minus) (.zero,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_8_3 (x y : ℂ) :
    exchangeNumerator x y (.minus,.minus) (.plus,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_8_4 (x y : ℂ) :
    exchangeNumerator x y (.minus,.minus) (.plus,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_8_5 (x y : ℂ) :
    exchangeNumerator x y (.minus,.minus) (.plus,.minus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_8_6 (x y : ℂ) :
    exchangeNumerator x y (.minus,.minus) (.minus,.zero) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_8_7 (x y : ℂ) :
    exchangeNumerator x y (.minus,.minus) (.minus,.plus) = 0 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]

theorem numerator_entry_8_8 (x y : ℂ) :
    exchangeNumerator x y (.minus,.minus) (.minus,.minus) = x^2-q^4*x*y-q^6*x*y-q^2*y^2 := by
  norm_num [exchangeNumerator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Pzero,Pone,Ptwo,Matrix.sub_apply,Matrix.one_apply,sum_spin,cup,insertion,charge,
    div_eq_mul_inv,zpow_neg,q_inv,q_five_inv,q_four_inv,
    xStar_polynomial,nZero_inv_polynomial,t,T]
  ring_nf
  simp only [q_pow_10]
  ring

theorem exchangeNumerator_eq_table (x y : ℂ) (a b : Pair) :
    exchangeNumerator x y a b = exchangeTable x y a b := by
  rcases a with ⟨a1,a2⟩; rcases b with ⟨b1,b2⟩
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2
  · exact numerator_entry_0_0 x y
  · exact numerator_entry_0_1 x y
  · exact numerator_entry_0_2 x y
  · exact numerator_entry_0_3 x y
  · exact numerator_entry_0_4 x y
  · exact numerator_entry_0_5 x y
  · exact numerator_entry_0_6 x y
  · exact numerator_entry_0_7 x y
  · exact numerator_entry_0_8 x y
  · exact numerator_entry_1_0 x y
  · exact numerator_entry_1_1 x y
  · exact numerator_entry_1_2 x y
  · exact numerator_entry_1_3 x y
  · exact numerator_entry_1_4 x y
  · exact numerator_entry_1_5 x y
  · exact numerator_entry_1_6 x y
  · exact numerator_entry_1_7 x y
  · exact numerator_entry_1_8 x y
  · exact numerator_entry_2_0 x y
  · exact numerator_entry_2_1 x y
  · exact numerator_entry_2_2 x y
  · exact numerator_entry_2_3 x y
  · exact numerator_entry_2_4 x y
  · exact numerator_entry_2_5 x y
  · exact numerator_entry_2_6 x y
  · exact numerator_entry_2_7 x y
  · exact numerator_entry_2_8 x y
  · exact numerator_entry_3_0 x y
  · exact numerator_entry_3_1 x y
  · exact numerator_entry_3_2 x y
  · exact numerator_entry_3_3 x y
  · exact numerator_entry_3_4 x y
  · exact numerator_entry_3_5 x y
  · exact numerator_entry_3_6 x y
  · exact numerator_entry_3_7 x y
  · exact numerator_entry_3_8 x y
  · exact numerator_entry_4_0 x y
  · exact numerator_entry_4_1 x y
  · exact numerator_entry_4_2 x y
  · exact numerator_entry_4_3 x y
  · exact numerator_entry_4_4 x y
  · exact numerator_entry_4_5 x y
  · exact numerator_entry_4_6 x y
  · exact numerator_entry_4_7 x y
  · exact numerator_entry_4_8 x y
  · exact numerator_entry_5_0 x y
  · exact numerator_entry_5_1 x y
  · exact numerator_entry_5_2 x y
  · exact numerator_entry_5_3 x y
  · exact numerator_entry_5_4 x y
  · exact numerator_entry_5_5 x y
  · exact numerator_entry_5_6 x y
  · exact numerator_entry_5_7 x y
  · exact numerator_entry_5_8 x y
  · exact numerator_entry_6_0 x y
  · exact numerator_entry_6_1 x y
  · exact numerator_entry_6_2 x y
  · exact numerator_entry_6_3 x y
  · exact numerator_entry_6_4 x y
  · exact numerator_entry_6_5 x y
  · exact numerator_entry_6_6 x y
  · exact numerator_entry_6_7 x y
  · exact numerator_entry_6_8 x y
  · exact numerator_entry_7_0 x y
  · exact numerator_entry_7_1 x y
  · exact numerator_entry_7_2 x y
  · exact numerator_entry_7_3 x y
  · exact numerator_entry_7_4 x y
  · exact numerator_entry_7_5 x y
  · exact numerator_entry_7_6 x y
  · exact numerator_entry_7_7 x y
  · exact numerator_entry_7_8 x y
  · exact numerator_entry_8_0 x y
  · exact numerator_entry_8_1 x y
  · exact numerator_entry_8_2 x y
  · exact numerator_entry_8_3 x y
  · exact numerator_entry_8_4 x y
  · exact numerator_entry_8_5 x y
  · exact numerator_entry_8_6 x y
  · exact numerator_entry_8_7 x y
  · exact numerator_entry_8_8 x y

end PolynomialVacuumAlgebra

end OAI
