import OAI.Combinatorics.PolynomialVacuum.Algebra.Table

namespace OAI

namespace PolynomialVacuumAlgebra

noncomputable def insertionTable : Pair → Spin → ℂ
  | (.zero,.zero), .zero => 1
  | (.zero,.plus), .plus => (1/2:ℂ)-(1/2:ℂ)*q^2+(1/2:ℂ)*q^4-(1/2:ℂ)*q^6
  | (.zero,.minus), .minus => (1/2:ℂ)+(1/2:ℂ)*q^2-(1/2:ℂ)*q^4+(1/2:ℂ)*q^6
  | (.plus,.zero), .plus => (1/2:ℂ)+(1/2:ℂ)*q^2-(1/2:ℂ)*q^4+(1/2:ℂ)*q^6
  | (.plus,.minus), .zero => -(1/2:ℂ)*q+(1/2:ℂ)*q^3+(1/2:ℂ)*q^5-(1/2:ℂ)*q^7
  | (.minus,.zero), .minus => (1/2:ℂ)-(1/2:ℂ)*q^2+(1/2:ℂ)*q^4-(1/2:ℂ)*q^6
  | (.minus,.plus), .zero => (1/2:ℂ)*q-(1/2:ℂ)*q^3-(1/2:ℂ)*q^5+(1/2:ℂ)*q^7
  | _, _ => 0

theorem insertion_eq_table (a : Pair) (h : Spin) : insertion a h = insertionTable a h := by
  rcases a with ⟨a,b⟩
  cases a <;> cases b <;> cases h <;>
    norm_num [insertion,insertionTable,charge,zpow_neg,q_inv,q_four_inv,xStar_polynomial]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_9,q_pow_10,q_pow_11,q_pow_12,q_pow_14]
  all_goals ring

 
noncomputable def cupSlideLeft (x : ℂ) (a b c h : Spin) : ℂ :=
  ∑ i : Spin, ∑ j : Spin, ∑ k : Spin,
    exchangeNumerator x 1 (a,b) (i,j) *
    exchangeNumerator (T*x) 1 (j,c) (k,h) * cup (i,k)

noncomputable def cupSlideRight (x : ℂ) (a b c h : Spin) : ℂ :=
  exchangeDenominator x 1 * exchangeDenominator (T*x) 1 *
    (if a=h then cup (b,c) else 0)

theorem cup_slide_entry_0_0 (x : ℂ) :
    cupSlideLeft x .zero .zero .zero .zero = cupSlideRight x .zero .zero .zero .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_24,q_pow_26,q_pow_28,q_pow_32]
  all_goals ring

theorem cup_slide_entry_0_1 (x : ℂ) :
    cupSlideLeft x .zero .zero .zero .plus = cupSlideRight x .zero .zero .zero .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_0_2 (x : ℂ) :
    cupSlideLeft x .zero .zero .zero .minus = cupSlideRight x .zero .zero .zero .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_1_0 (x : ℂ) :
    cupSlideLeft x .zero .zero .plus .zero = cupSlideRight x .zero .zero .plus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_1_1 (x : ℂ) :
    cupSlideLeft x .zero .zero .plus .plus = cupSlideRight x .zero .zero .plus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20]
  all_goals ring

theorem cup_slide_entry_1_2 (x : ℂ) :
    cupSlideLeft x .zero .zero .plus .minus = cupSlideRight x .zero .zero .plus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_2_0 (x : ℂ) :
    cupSlideLeft x .zero .zero .minus .zero = cupSlideRight x .zero .zero .minus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_2_1 (x : ℂ) :
    cupSlideLeft x .zero .zero .minus .plus = cupSlideRight x .zero .zero .minus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_2_2 (x : ℂ) :
    cupSlideLeft x .zero .zero .minus .minus = cupSlideRight x .zero .zero .minus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_24,q_pow_26]
  all_goals ring

theorem cup_slide_entry_3_0 (x : ℂ) :
    cupSlideLeft x .zero .plus .zero .zero = cupSlideRight x .zero .plus .zero .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_3_1 (x : ℂ) :
    cupSlideLeft x .zero .plus .zero .plus = cupSlideRight x .zero .plus .zero .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20]
  all_goals ring

theorem cup_slide_entry_3_2 (x : ℂ) :
    cupSlideLeft x .zero .plus .zero .minus = cupSlideRight x .zero .plus .zero .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_4_0 (x : ℂ) :
    cupSlideLeft x .zero .plus .plus .zero = cupSlideRight x .zero .plus .plus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_4_1 (x : ℂ) :
    cupSlideLeft x .zero .plus .plus .plus = cupSlideRight x .zero .plus .plus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_4_2 (x : ℂ) :
    cupSlideLeft x .zero .plus .plus .minus = cupSlideRight x .zero .plus .plus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_5_0 (x : ℂ) :
    cupSlideLeft x .zero .plus .minus .zero = cupSlideRight x .zero .plus .minus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17,q_pow_19,q_pow_21,q_pow_23,q_pow_25,q_pow_27,q_pow_31,q_pow_33,q_pow_37]
  all_goals ring

theorem cup_slide_entry_5_1 (x : ℂ) :
    cupSlideLeft x .zero .plus .minus .plus = cupSlideRight x .zero .plus .minus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_5_2 (x : ℂ) :
    cupSlideLeft x .zero .plus .minus .minus = cupSlideRight x .zero .plus .minus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_6_0 (x : ℂ) :
    cupSlideLeft x .zero .minus .zero .zero = cupSlideRight x .zero .minus .zero .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_6_1 (x : ℂ) :
    cupSlideLeft x .zero .minus .zero .plus = cupSlideRight x .zero .minus .zero .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_6_2 (x : ℂ) :
    cupSlideLeft x .zero .minus .zero .minus = cupSlideRight x .zero .minus .zero .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22]
  all_goals ring

theorem cup_slide_entry_7_0 (x : ℂ) :
    cupSlideLeft x .zero .minus .plus .zero = cupSlideRight x .zero .minus .plus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17,q_pow_19,q_pow_21,q_pow_23,q_pow_25,q_pow_29,q_pow_31,q_pow_35]
  all_goals ring

theorem cup_slide_entry_7_1 (x : ℂ) :
    cupSlideLeft x .zero .minus .plus .plus = cupSlideRight x .zero .minus .plus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_7_2 (x : ℂ) :
    cupSlideLeft x .zero .minus .plus .minus = cupSlideRight x .zero .minus .plus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_8_0 (x : ℂ) :
    cupSlideLeft x .zero .minus .minus .zero = cupSlideRight x .zero .minus .minus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_8_1 (x : ℂ) :
    cupSlideLeft x .zero .minus .minus .plus = cupSlideRight x .zero .minus .minus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_8_2 (x : ℂ) :
    cupSlideLeft x .zero .minus .minus .minus = cupSlideRight x .zero .minus .minus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_9_0 (x : ℂ) :
    cupSlideLeft x .plus .zero .zero .zero = cupSlideRight x .plus .zero .zero .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_9_1 (x : ℂ) :
    cupSlideLeft x .plus .zero .zero .plus = cupSlideRight x .plus .zero .zero .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_26,q_pow_28,q_pow_32]
  all_goals ring

theorem cup_slide_entry_9_2 (x : ℂ) :
    cupSlideLeft x .plus .zero .zero .minus = cupSlideRight x .plus .zero .zero .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_10_0 (x : ℂ) :
    cupSlideLeft x .plus .zero .plus .zero = cupSlideRight x .plus .zero .plus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_10_1 (x : ℂ) :
    cupSlideLeft x .plus .zero .plus .plus = cupSlideRight x .plus .zero .plus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_10_2 (x : ℂ) :
    cupSlideLeft x .plus .zero .plus .minus = cupSlideRight x .plus .zero .plus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_11_0 (x : ℂ) :
    cupSlideLeft x .plus .zero .minus .zero = cupSlideRight x .plus .zero .minus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_19,q_pow_21,q_pow_23,q_pow_25]
  all_goals ring

theorem cup_slide_entry_11_1 (x : ℂ) :
    cupSlideLeft x .plus .zero .minus .plus = cupSlideRight x .plus .zero .minus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_11_2 (x : ℂ) :
    cupSlideLeft x .plus .zero .minus .minus = cupSlideRight x .plus .zero .minus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_12_0 (x : ℂ) :
    cupSlideLeft x .plus .plus .zero .zero = cupSlideRight x .plus .plus .zero .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_12_1 (x : ℂ) :
    cupSlideLeft x .plus .plus .zero .plus = cupSlideRight x .plus .plus .zero .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_12_2 (x : ℂ) :
    cupSlideLeft x .plus .plus .zero .minus = cupSlideRight x .plus .plus .zero .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_13_0 (x : ℂ) :
    cupSlideLeft x .plus .plus .plus .zero = cupSlideRight x .plus .plus .plus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_13_1 (x : ℂ) :
    cupSlideLeft x .plus .plus .plus .plus = cupSlideRight x .plus .plus .plus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_13_2 (x : ℂ) :
    cupSlideLeft x .plus .plus .plus .minus = cupSlideRight x .plus .plus .plus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_14_0 (x : ℂ) :
    cupSlideLeft x .plus .plus .minus .zero = cupSlideRight x .plus .plus .minus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_14_1 (x : ℂ) :
    cupSlideLeft x .plus .plus .minus .plus = cupSlideRight x .plus .plus .minus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try (apply Or.inl)
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_26,q_pow_28,q_pow_32]
  all_goals ring

theorem cup_slide_entry_14_2 (x : ℂ) :
    cupSlideLeft x .plus .plus .minus .minus = cupSlideRight x .plus .plus .minus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_15_0 (x : ℂ) :
    cupSlideLeft x .plus .minus .zero .zero = cupSlideRight x .plus .minus .zero .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17,q_pow_19,q_pow_21,q_pow_23,q_pow_25]
  all_goals ring

theorem cup_slide_entry_15_1 (x : ℂ) :
    cupSlideLeft x .plus .minus .zero .plus = cupSlideRight x .plus .minus .zero .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_15_2 (x : ℂ) :
    cupSlideLeft x .plus .minus .zero .minus = cupSlideRight x .plus .minus .zero .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_16_0 (x : ℂ) :
    cupSlideLeft x .plus .minus .plus .zero = cupSlideRight x .plus .minus .plus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_16_1 (x : ℂ) :
    cupSlideLeft x .plus .minus .plus .plus = cupSlideRight x .plus .minus .plus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17,q_pow_19,q_pow_21,q_pow_23,q_pow_25,q_pow_29,q_pow_31,q_pow_35]
  all_goals ring

theorem cup_slide_entry_16_2 (x : ℂ) :
    cupSlideLeft x .plus .minus .plus .minus = cupSlideRight x .plus .minus .plus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_17_0 (x : ℂ) :
    cupSlideLeft x .plus .minus .minus .zero = cupSlideRight x .plus .minus .minus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_17_1 (x : ℂ) :
    cupSlideLeft x .plus .minus .minus .plus = cupSlideRight x .plus .minus .minus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_17_2 (x : ℂ) :
    cupSlideLeft x .plus .minus .minus .minus = cupSlideRight x .plus .minus .minus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17,q_pow_19,q_pow_21,q_pow_23,q_pow_25,q_pow_27]
  all_goals ring

theorem cup_slide_entry_18_0 (x : ℂ) :
    cupSlideLeft x .minus .zero .zero .zero = cupSlideRight x .minus .zero .zero .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_18_1 (x : ℂ) :
    cupSlideLeft x .minus .zero .zero .plus = cupSlideRight x .minus .zero .zero .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_18_2 (x : ℂ) :
    cupSlideLeft x .minus .zero .zero .minus = cupSlideRight x .minus .zero .zero .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_24,q_pow_26,q_pow_28,q_pow_32]
  all_goals ring

theorem cup_slide_entry_19_0 (x : ℂ) :
    cupSlideLeft x .minus .zero .plus .zero = cupSlideRight x .minus .zero .plus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17,q_pow_19,q_pow_21,q_pow_23]
  all_goals ring

theorem cup_slide_entry_19_1 (x : ℂ) :
    cupSlideLeft x .minus .zero .plus .plus = cupSlideRight x .minus .zero .plus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_19_2 (x : ℂ) :
    cupSlideLeft x .minus .zero .plus .minus = cupSlideRight x .minus .zero .plus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_20_0 (x : ℂ) :
    cupSlideLeft x .minus .zero .minus .zero = cupSlideRight x .minus .zero .minus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_20_1 (x : ℂ) :
    cupSlideLeft x .minus .zero .minus .plus = cupSlideRight x .minus .zero .minus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_20_2 (x : ℂ) :
    cupSlideLeft x .minus .zero .minus .minus = cupSlideRight x .minus .zero .minus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_21_0 (x : ℂ) :
    cupSlideLeft x .minus .plus .zero .zero = cupSlideRight x .minus .plus .zero .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_11,q_pow_13,q_pow_15,q_pow_17,q_pow_19,q_pow_21,q_pow_23,q_pow_25]
  all_goals ring

theorem cup_slide_entry_21_1 (x : ℂ) :
    cupSlideLeft x .minus .plus .zero .plus = cupSlideRight x .minus .plus .zero .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_21_2 (x : ℂ) :
    cupSlideLeft x .minus .plus .zero .minus = cupSlideRight x .minus .plus .zero .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_22_0 (x : ℂ) :
    cupSlideLeft x .minus .plus .plus .zero = cupSlideRight x .minus .plus .plus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_22_1 (x : ℂ) :
    cupSlideLeft x .minus .plus .plus .plus = cupSlideRight x .minus .plus .plus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17,q_pow_19,q_pow_21]
  all_goals ring

theorem cup_slide_entry_22_2 (x : ℂ) :
    cupSlideLeft x .minus .plus .plus .minus = cupSlideRight x .minus .plus .plus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_23_0 (x : ℂ) :
    cupSlideLeft x .minus .plus .minus .zero = cupSlideRight x .minus .plus .minus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_23_1 (x : ℂ) :
    cupSlideLeft x .minus .plus .minus .plus = cupSlideRight x .minus .plus .minus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_23_2 (x : ℂ) :
    cupSlideLeft x .minus .plus .minus .minus = cupSlideRight x .minus .plus .minus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17,q_pow_19,q_pow_21,q_pow_23,q_pow_25,q_pow_27,q_pow_31,q_pow_33,q_pow_37]
  all_goals ring

theorem cup_slide_entry_24_0 (x : ℂ) :
    cupSlideLeft x .minus .minus .zero .zero = cupSlideRight x .minus .minus .zero .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_24_1 (x : ℂ) :
    cupSlideLeft x .minus .minus .zero .plus = cupSlideRight x .minus .minus .zero .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_24_2 (x : ℂ) :
    cupSlideLeft x .minus .minus .zero .minus = cupSlideRight x .minus .minus .zero .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_25_0 (x : ℂ) :
    cupSlideLeft x .minus .minus .plus .zero = cupSlideRight x .minus .minus .plus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_25_1 (x : ℂ) :
    cupSlideLeft x .minus .minus .plus .plus = cupSlideRight x .minus .minus .plus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_25_2 (x : ℂ) :
    cupSlideLeft x .minus .minus .plus .minus = cupSlideRight x .minus .minus .plus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try (apply Or.inl)
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18,q_pow_20,q_pow_22,q_pow_26,q_pow_28,q_pow_32]
  all_goals ring

theorem cup_slide_entry_26_0 (x : ℂ) :
    cupSlideLeft x .minus .minus .minus .zero = cupSlideRight x .minus .minus .minus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_26_1 (x : ℂ) :
    cupSlideLeft x .minus .minus .minus .plus = cupSlideRight x .minus .minus .minus .plus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_entry_26_2 (x : ℂ) :
    cupSlideLeft x .minus .minus .minus .minus = cupSlideRight x .minus .minus .minus .minus := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]

theorem cup_slide_coefficients (x : ℂ) (a b c h : Spin) :
    cupSlideLeft x a b c h = cupSlideRight x a b c h := by
  cases a <;> cases b <;> cases c <;> cases h
  · exact cup_slide_entry_0_0 x
  · exact cup_slide_entry_0_1 x
  · exact cup_slide_entry_0_2 x
  · exact cup_slide_entry_1_0 x
  · exact cup_slide_entry_1_1 x
  · exact cup_slide_entry_1_2 x
  · exact cup_slide_entry_2_0 x
  · exact cup_slide_entry_2_1 x
  · exact cup_slide_entry_2_2 x
  · exact cup_slide_entry_3_0 x
  · exact cup_slide_entry_3_1 x
  · exact cup_slide_entry_3_2 x
  · exact cup_slide_entry_4_0 x
  · exact cup_slide_entry_4_1 x
  · exact cup_slide_entry_4_2 x
  · exact cup_slide_entry_5_0 x
  · exact cup_slide_entry_5_1 x
  · exact cup_slide_entry_5_2 x
  · exact cup_slide_entry_6_0 x
  · exact cup_slide_entry_6_1 x
  · exact cup_slide_entry_6_2 x
  · exact cup_slide_entry_7_0 x
  · exact cup_slide_entry_7_1 x
  · exact cup_slide_entry_7_2 x
  · exact cup_slide_entry_8_0 x
  · exact cup_slide_entry_8_1 x
  · exact cup_slide_entry_8_2 x
  · exact cup_slide_entry_9_0 x
  · exact cup_slide_entry_9_1 x
  · exact cup_slide_entry_9_2 x
  · exact cup_slide_entry_10_0 x
  · exact cup_slide_entry_10_1 x
  · exact cup_slide_entry_10_2 x
  · exact cup_slide_entry_11_0 x
  · exact cup_slide_entry_11_1 x
  · exact cup_slide_entry_11_2 x
  · exact cup_slide_entry_12_0 x
  · exact cup_slide_entry_12_1 x
  · exact cup_slide_entry_12_2 x
  · exact cup_slide_entry_13_0 x
  · exact cup_slide_entry_13_1 x
  · exact cup_slide_entry_13_2 x
  · exact cup_slide_entry_14_0 x
  · exact cup_slide_entry_14_1 x
  · exact cup_slide_entry_14_2 x
  · exact cup_slide_entry_15_0 x
  · exact cup_slide_entry_15_1 x
  · exact cup_slide_entry_15_2 x
  · exact cup_slide_entry_16_0 x
  · exact cup_slide_entry_16_1 x
  · exact cup_slide_entry_16_2 x
  · exact cup_slide_entry_17_0 x
  · exact cup_slide_entry_17_1 x
  · exact cup_slide_entry_17_2 x
  · exact cup_slide_entry_18_0 x
  · exact cup_slide_entry_18_1 x
  · exact cup_slide_entry_18_2 x
  · exact cup_slide_entry_19_0 x
  · exact cup_slide_entry_19_1 x
  · exact cup_slide_entry_19_2 x
  · exact cup_slide_entry_20_0 x
  · exact cup_slide_entry_20_1 x
  · exact cup_slide_entry_20_2 x
  · exact cup_slide_entry_21_0 x
  · exact cup_slide_entry_21_1 x
  · exact cup_slide_entry_21_2 x
  · exact cup_slide_entry_22_0 x
  · exact cup_slide_entry_22_1 x
  · exact cup_slide_entry_22_2 x
  · exact cup_slide_entry_23_0 x
  · exact cup_slide_entry_23_1 x
  · exact cup_slide_entry_23_2 x
  · exact cup_slide_entry_24_0 x
  · exact cup_slide_entry_24_1 x
  · exact cup_slide_entry_24_2 x
  · exact cup_slide_entry_25_0 x
  · exact cup_slide_entry_25_1 x
  · exact cup_slide_entry_25_2 x
  · exact cup_slide_entry_26_0 x
  · exact cup_slide_entry_26_1 x
  · exact cup_slide_entry_26_2 x

end PolynomialVacuumAlgebra

end OAI
