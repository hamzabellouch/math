import OAI.Combinatorics.PolynomialVacuum.Algebra.CupSlide
import OAI.Combinatorics.PolynomialVacuum.Algebra.Ring

namespace OAI

namespace PolynomialVacuumAlgebra

 
noncomputable def insertionSlideLeft (x : ℂ) (a b c h k : Spin) : ℂ :=
  exchangeDenominator (t*x) 1 *
  ∑ i : Spin, ∑ j : Spin, ∑ l : Spin,
    exchangeNumerator x 1 (a,b) (i,j) *
    exchangeNumerator (t^2*x) 1 (j,c) (l,k) * insertion (i,l) h

noncomputable def insertionSlideRight (x : ℂ) (a b c h k : Spin) : ℂ :=
  exchangeDenominator x 1 * exchangeDenominator (t^2*x) 1 *
  ∑ g : Spin, insertion (b,c) g * exchangeNumerator (t*x) 1 (a,g) (h,k)

theorem insertion_slide_entry_0_0 (x : ℂ) :
    insertionSlideLeft x .zero .zero .zero .zero .zero = insertionSlideRight x .zero .zero .zero .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_0_1 (x : ℂ) :
    insertionSlideLeft x .zero .zero .zero .zero .plus = insertionSlideRight x .zero .zero .zero .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_0_2 (x : ℂ) :
    insertionSlideLeft x .zero .zero .zero .zero .minus = insertionSlideRight x .zero .zero .zero .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_0_3 (x : ℂ) :
    insertionSlideLeft x .zero .zero .zero .plus .zero = insertionSlideRight x .zero .zero .zero .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_0_4 (x : ℂ) :
    insertionSlideLeft x .zero .zero .zero .plus .plus = insertionSlideRight x .zero .zero .zero .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_0_5 (x : ℂ) :
    insertionSlideLeft x .zero .zero .zero .plus .minus = insertionSlideRight x .zero .zero .zero .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_0_6 (x : ℂ) :
    insertionSlideLeft x .zero .zero .zero .minus .zero = insertionSlideRight x .zero .zero .zero .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_0_7 (x : ℂ) :
    insertionSlideLeft x .zero .zero .zero .minus .plus = insertionSlideRight x .zero .zero .zero .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_0_8 (x : ℂ) :
    insertionSlideLeft x .zero .zero .zero .minus .minus = insertionSlideRight x .zero .zero .zero .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_1_0 (x : ℂ) :
    insertionSlideLeft x .zero .zero .plus .zero .zero = insertionSlideRight x .zero .zero .plus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_1_1 (x : ℂ) :
    insertionSlideLeft x .zero .zero .plus .zero .plus = insertionSlideRight x .zero .zero .plus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_1_2 (x : ℂ) :
    insertionSlideLeft x .zero .zero .plus .zero .minus = insertionSlideRight x .zero .zero .plus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_1_3 (x : ℂ) :
    insertionSlideLeft x .zero .zero .plus .plus .zero = insertionSlideRight x .zero .zero .plus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_1_4 (x : ℂ) :
    insertionSlideLeft x .zero .zero .plus .plus .plus = insertionSlideRight x .zero .zero .plus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_1_5 (x : ℂ) :
    insertionSlideLeft x .zero .zero .plus .plus .minus = insertionSlideRight x .zero .zero .plus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_1_6 (x : ℂ) :
    insertionSlideLeft x .zero .zero .plus .minus .zero = insertionSlideRight x .zero .zero .plus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_1_7 (x : ℂ) :
    insertionSlideLeft x .zero .zero .plus .minus .plus = insertionSlideRight x .zero .zero .plus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_1_8 (x : ℂ) :
    insertionSlideLeft x .zero .zero .plus .minus .minus = insertionSlideRight x .zero .zero .plus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_2_0 (x : ℂ) :
    insertionSlideLeft x .zero .zero .minus .zero .zero = insertionSlideRight x .zero .zero .minus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_2_1 (x : ℂ) :
    insertionSlideLeft x .zero .zero .minus .zero .plus = insertionSlideRight x .zero .zero .minus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_2_2 (x : ℂ) :
    insertionSlideLeft x .zero .zero .minus .zero .minus = insertionSlideRight x .zero .zero .minus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_2_3 (x : ℂ) :
    insertionSlideLeft x .zero .zero .minus .plus .zero = insertionSlideRight x .zero .zero .minus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_2_4 (x : ℂ) :
    insertionSlideLeft x .zero .zero .minus .plus .plus = insertionSlideRight x .zero .zero .minus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_2_5 (x : ℂ) :
    insertionSlideLeft x .zero .zero .minus .plus .minus = insertionSlideRight x .zero .zero .minus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_2_6 (x : ℂ) :
    insertionSlideLeft x .zero .zero .minus .minus .zero = insertionSlideRight x .zero .zero .minus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_2_7 (x : ℂ) :
    insertionSlideLeft x .zero .zero .minus .minus .plus = insertionSlideRight x .zero .zero .minus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_2_8 (x : ℂ) :
    insertionSlideLeft x .zero .zero .minus .minus .minus = insertionSlideRight x .zero .zero .minus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_3_0 (x : ℂ) :
    insertionSlideLeft x .zero .plus .zero .zero .zero = insertionSlideRight x .zero .plus .zero .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_3_1 (x : ℂ) :
    insertionSlideLeft x .zero .plus .zero .zero .plus = insertionSlideRight x .zero .plus .zero .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_3_2 (x : ℂ) :
    insertionSlideLeft x .zero .plus .zero .zero .minus = insertionSlideRight x .zero .plus .zero .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_3_3 (x : ℂ) :
    insertionSlideLeft x .zero .plus .zero .plus .zero = insertionSlideRight x .zero .plus .zero .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_3_4 (x : ℂ) :
    insertionSlideLeft x .zero .plus .zero .plus .plus = insertionSlideRight x .zero .plus .zero .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_3_5 (x : ℂ) :
    insertionSlideLeft x .zero .plus .zero .plus .minus = insertionSlideRight x .zero .plus .zero .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_3_6 (x : ℂ) :
    insertionSlideLeft x .zero .plus .zero .minus .zero = insertionSlideRight x .zero .plus .zero .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_3_7 (x : ℂ) :
    insertionSlideLeft x .zero .plus .zero .minus .plus = insertionSlideRight x .zero .plus .zero .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_3_8 (x : ℂ) :
    insertionSlideLeft x .zero .plus .zero .minus .minus = insertionSlideRight x .zero .plus .zero .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_4_0 (x : ℂ) :
    insertionSlideLeft x .zero .plus .plus .zero .zero = insertionSlideRight x .zero .plus .plus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_4_1 (x : ℂ) :
    insertionSlideLeft x .zero .plus .plus .zero .plus = insertionSlideRight x .zero .plus .plus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_4_2 (x : ℂ) :
    insertionSlideLeft x .zero .plus .plus .zero .minus = insertionSlideRight x .zero .plus .plus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_4_3 (x : ℂ) :
    insertionSlideLeft x .zero .plus .plus .plus .zero = insertionSlideRight x .zero .plus .plus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_4_4 (x : ℂ) :
    insertionSlideLeft x .zero .plus .plus .plus .plus = insertionSlideRight x .zero .plus .plus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_4_5 (x : ℂ) :
    insertionSlideLeft x .zero .plus .plus .plus .minus = insertionSlideRight x .zero .plus .plus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_4_6 (x : ℂ) :
    insertionSlideLeft x .zero .plus .plus .minus .zero = insertionSlideRight x .zero .plus .plus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_4_7 (x : ℂ) :
    insertionSlideLeft x .zero .plus .plus .minus .plus = insertionSlideRight x .zero .plus .plus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_4_8 (x : ℂ) :
    insertionSlideLeft x .zero .plus .plus .minus .minus = insertionSlideRight x .zero .plus .plus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_5_0 (x : ℂ) :
    insertionSlideLeft x .zero .plus .minus .zero .zero = insertionSlideRight x .zero .plus .minus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_5_1 (x : ℂ) :
    insertionSlideLeft x .zero .plus .minus .zero .plus = insertionSlideRight x .zero .plus .minus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_5_2 (x : ℂ) :
    insertionSlideLeft x .zero .plus .minus .zero .minus = insertionSlideRight x .zero .plus .minus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_5_3 (x : ℂ) :
    insertionSlideLeft x .zero .plus .minus .plus .zero = insertionSlideRight x .zero .plus .minus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_5_4 (x : ℂ) :
    insertionSlideLeft x .zero .plus .minus .plus .plus = insertionSlideRight x .zero .plus .minus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_5_5 (x : ℂ) :
    insertionSlideLeft x .zero .plus .minus .plus .minus = insertionSlideRight x .zero .plus .minus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_5_6 (x : ℂ) :
    insertionSlideLeft x .zero .plus .minus .minus .zero = insertionSlideRight x .zero .plus .minus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_5_7 (x : ℂ) :
    insertionSlideLeft x .zero .plus .minus .minus .plus = insertionSlideRight x .zero .plus .minus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_5_8 (x : ℂ) :
    insertionSlideLeft x .zero .plus .minus .minus .minus = insertionSlideRight x .zero .plus .minus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_6_0 (x : ℂ) :
    insertionSlideLeft x .zero .minus .zero .zero .zero = insertionSlideRight x .zero .minus .zero .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_6_1 (x : ℂ) :
    insertionSlideLeft x .zero .minus .zero .zero .plus = insertionSlideRight x .zero .minus .zero .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_6_2 (x : ℂ) :
    insertionSlideLeft x .zero .minus .zero .zero .minus = insertionSlideRight x .zero .minus .zero .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_6_3 (x : ℂ) :
    insertionSlideLeft x .zero .minus .zero .plus .zero = insertionSlideRight x .zero .minus .zero .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_6_4 (x : ℂ) :
    insertionSlideLeft x .zero .minus .zero .plus .plus = insertionSlideRight x .zero .minus .zero .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_6_5 (x : ℂ) :
    insertionSlideLeft x .zero .minus .zero .plus .minus = insertionSlideRight x .zero .minus .zero .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_6_6 (x : ℂ) :
    insertionSlideLeft x .zero .minus .zero .minus .zero = insertionSlideRight x .zero .minus .zero .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_6_7 (x : ℂ) :
    insertionSlideLeft x .zero .minus .zero .minus .plus = insertionSlideRight x .zero .minus .zero .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_6_8 (x : ℂ) :
    insertionSlideLeft x .zero .minus .zero .minus .minus = insertionSlideRight x .zero .minus .zero .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_7_0 (x : ℂ) :
    insertionSlideLeft x .zero .minus .plus .zero .zero = insertionSlideRight x .zero .minus .plus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_7_1 (x : ℂ) :
    insertionSlideLeft x .zero .minus .plus .zero .plus = insertionSlideRight x .zero .minus .plus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_7_2 (x : ℂ) :
    insertionSlideLeft x .zero .minus .plus .zero .minus = insertionSlideRight x .zero .minus .plus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_7_3 (x : ℂ) :
    insertionSlideLeft x .zero .minus .plus .plus .zero = insertionSlideRight x .zero .minus .plus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_7_4 (x : ℂ) :
    insertionSlideLeft x .zero .minus .plus .plus .plus = insertionSlideRight x .zero .minus .plus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_7_5 (x : ℂ) :
    insertionSlideLeft x .zero .minus .plus .plus .minus = insertionSlideRight x .zero .minus .plus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_7_6 (x : ℂ) :
    insertionSlideLeft x .zero .minus .plus .minus .zero = insertionSlideRight x .zero .minus .plus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_7_7 (x : ℂ) :
    insertionSlideLeft x .zero .minus .plus .minus .plus = insertionSlideRight x .zero .minus .plus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_7_8 (x : ℂ) :
    insertionSlideLeft x .zero .minus .plus .minus .minus = insertionSlideRight x .zero .minus .plus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_8_0 (x : ℂ) :
    insertionSlideLeft x .zero .minus .minus .zero .zero = insertionSlideRight x .zero .minus .minus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_8_1 (x : ℂ) :
    insertionSlideLeft x .zero .minus .minus .zero .plus = insertionSlideRight x .zero .minus .minus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_8_2 (x : ℂ) :
    insertionSlideLeft x .zero .minus .minus .zero .minus = insertionSlideRight x .zero .minus .minus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_8_3 (x : ℂ) :
    insertionSlideLeft x .zero .minus .minus .plus .zero = insertionSlideRight x .zero .minus .minus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_8_4 (x : ℂ) :
    insertionSlideLeft x .zero .minus .minus .plus .plus = insertionSlideRight x .zero .minus .minus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_8_5 (x : ℂ) :
    insertionSlideLeft x .zero .minus .minus .plus .minus = insertionSlideRight x .zero .minus .minus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_8_6 (x : ℂ) :
    insertionSlideLeft x .zero .minus .minus .minus .zero = insertionSlideRight x .zero .minus .minus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_8_7 (x : ℂ) :
    insertionSlideLeft x .zero .minus .minus .minus .plus = insertionSlideRight x .zero .minus .minus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_8_8 (x : ℂ) :
    insertionSlideLeft x .zero .minus .minus .minus .minus = insertionSlideRight x .zero .minus .minus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_9_0 (x : ℂ) :
    insertionSlideLeft x .plus .zero .zero .zero .zero = insertionSlideRight x .plus .zero .zero .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_9_1 (x : ℂ) :
    insertionSlideLeft x .plus .zero .zero .zero .plus = insertionSlideRight x .plus .zero .zero .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_9_2 (x : ℂ) :
    insertionSlideLeft x .plus .zero .zero .zero .minus = insertionSlideRight x .plus .zero .zero .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_9_3 (x : ℂ) :
    insertionSlideLeft x .plus .zero .zero .plus .zero = insertionSlideRight x .plus .zero .zero .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_9_4 (x : ℂ) :
    insertionSlideLeft x .plus .zero .zero .plus .plus = insertionSlideRight x .plus .zero .zero .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_9_5 (x : ℂ) :
    insertionSlideLeft x .plus .zero .zero .plus .minus = insertionSlideRight x .plus .zero .zero .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_9_6 (x : ℂ) :
    insertionSlideLeft x .plus .zero .zero .minus .zero = insertionSlideRight x .plus .zero .zero .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_9_7 (x : ℂ) :
    insertionSlideLeft x .plus .zero .zero .minus .plus = insertionSlideRight x .plus .zero .zero .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_9_8 (x : ℂ) :
    insertionSlideLeft x .plus .zero .zero .minus .minus = insertionSlideRight x .plus .zero .zero .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_10_0 (x : ℂ) :
    insertionSlideLeft x .plus .zero .plus .zero .zero = insertionSlideRight x .plus .zero .plus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_10_1 (x : ℂ) :
    insertionSlideLeft x .plus .zero .plus .zero .plus = insertionSlideRight x .plus .zero .plus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_10_2 (x : ℂ) :
    insertionSlideLeft x .plus .zero .plus .zero .minus = insertionSlideRight x .plus .zero .plus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_10_3 (x : ℂ) :
    insertionSlideLeft x .plus .zero .plus .plus .zero = insertionSlideRight x .plus .zero .plus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_10_4 (x : ℂ) :
    insertionSlideLeft x .plus .zero .plus .plus .plus = insertionSlideRight x .plus .zero .plus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_10_5 (x : ℂ) :
    insertionSlideLeft x .plus .zero .plus .plus .minus = insertionSlideRight x .plus .zero .plus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_10_6 (x : ℂ) :
    insertionSlideLeft x .plus .zero .plus .minus .zero = insertionSlideRight x .plus .zero .plus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_10_7 (x : ℂ) :
    insertionSlideLeft x .plus .zero .plus .minus .plus = insertionSlideRight x .plus .zero .plus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_10_8 (x : ℂ) :
    insertionSlideLeft x .plus .zero .plus .minus .minus = insertionSlideRight x .plus .zero .plus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_11_0 (x : ℂ) :
    insertionSlideLeft x .plus .zero .minus .zero .zero = insertionSlideRight x .plus .zero .minus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_11_1 (x : ℂ) :
    insertionSlideLeft x .plus .zero .minus .zero .plus = insertionSlideRight x .plus .zero .minus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_11_2 (x : ℂ) :
    insertionSlideLeft x .plus .zero .minus .zero .minus = insertionSlideRight x .plus .zero .minus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_11_3 (x : ℂ) :
    insertionSlideLeft x .plus .zero .minus .plus .zero = insertionSlideRight x .plus .zero .minus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_11_4 (x : ℂ) :
    insertionSlideLeft x .plus .zero .minus .plus .plus = insertionSlideRight x .plus .zero .minus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_11_5 (x : ℂ) :
    insertionSlideLeft x .plus .zero .minus .plus .minus = insertionSlideRight x .plus .zero .minus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_11_6 (x : ℂ) :
    insertionSlideLeft x .plus .zero .minus .minus .zero = insertionSlideRight x .plus .zero .minus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_11_7 (x : ℂ) :
    insertionSlideLeft x .plus .zero .minus .minus .plus = insertionSlideRight x .plus .zero .minus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_11_8 (x : ℂ) :
    insertionSlideLeft x .plus .zero .minus .minus .minus = insertionSlideRight x .plus .zero .minus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_12_0 (x : ℂ) :
    insertionSlideLeft x .plus .plus .zero .zero .zero = insertionSlideRight x .plus .plus .zero .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_12_1 (x : ℂ) :
    insertionSlideLeft x .plus .plus .zero .zero .plus = insertionSlideRight x .plus .plus .zero .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_12_2 (x : ℂ) :
    insertionSlideLeft x .plus .plus .zero .zero .minus = insertionSlideRight x .plus .plus .zero .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_12_3 (x : ℂ) :
    insertionSlideLeft x .plus .plus .zero .plus .zero = insertionSlideRight x .plus .plus .zero .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_12_4 (x : ℂ) :
    insertionSlideLeft x .plus .plus .zero .plus .plus = insertionSlideRight x .plus .plus .zero .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_12_5 (x : ℂ) :
    insertionSlideLeft x .plus .plus .zero .plus .minus = insertionSlideRight x .plus .plus .zero .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_12_6 (x : ℂ) :
    insertionSlideLeft x .plus .plus .zero .minus .zero = insertionSlideRight x .plus .plus .zero .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_12_7 (x : ℂ) :
    insertionSlideLeft x .plus .plus .zero .minus .plus = insertionSlideRight x .plus .plus .zero .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_12_8 (x : ℂ) :
    insertionSlideLeft x .plus .plus .zero .minus .minus = insertionSlideRight x .plus .plus .zero .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_13_0 (x : ℂ) :
    insertionSlideLeft x .plus .plus .plus .zero .zero = insertionSlideRight x .plus .plus .plus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_13_1 (x : ℂ) :
    insertionSlideLeft x .plus .plus .plus .zero .plus = insertionSlideRight x .plus .plus .plus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_13_2 (x : ℂ) :
    insertionSlideLeft x .plus .plus .plus .zero .minus = insertionSlideRight x .plus .plus .plus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_13_3 (x : ℂ) :
    insertionSlideLeft x .plus .plus .plus .plus .zero = insertionSlideRight x .plus .plus .plus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_13_4 (x : ℂ) :
    insertionSlideLeft x .plus .plus .plus .plus .plus = insertionSlideRight x .plus .plus .plus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_13_5 (x : ℂ) :
    insertionSlideLeft x .plus .plus .plus .plus .minus = insertionSlideRight x .plus .plus .plus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_13_6 (x : ℂ) :
    insertionSlideLeft x .plus .plus .plus .minus .zero = insertionSlideRight x .plus .plus .plus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_13_7 (x : ℂ) :
    insertionSlideLeft x .plus .plus .plus .minus .plus = insertionSlideRight x .plus .plus .plus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_13_8 (x : ℂ) :
    insertionSlideLeft x .plus .plus .plus .minus .minus = insertionSlideRight x .plus .plus .plus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_14_0 (x : ℂ) :
    insertionSlideLeft x .plus .plus .minus .zero .zero = insertionSlideRight x .plus .plus .minus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_14_1 (x : ℂ) :
    insertionSlideLeft x .plus .plus .minus .zero .plus = insertionSlideRight x .plus .plus .minus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_14_2 (x : ℂ) :
    insertionSlideLeft x .plus .plus .minus .zero .minus = insertionSlideRight x .plus .plus .minus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_14_3 (x : ℂ) :
    insertionSlideLeft x .plus .plus .minus .plus .zero = insertionSlideRight x .plus .plus .minus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_14_4 (x : ℂ) :
    insertionSlideLeft x .plus .plus .minus .plus .plus = insertionSlideRight x .plus .plus .minus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_14_5 (x : ℂ) :
    insertionSlideLeft x .plus .plus .minus .plus .minus = insertionSlideRight x .plus .plus .minus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_14_6 (x : ℂ) :
    insertionSlideLeft x .plus .plus .minus .minus .zero = insertionSlideRight x .plus .plus .minus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_14_7 (x : ℂ) :
    insertionSlideLeft x .plus .plus .minus .minus .plus = insertionSlideRight x .plus .plus .minus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_14_8 (x : ℂ) :
    insertionSlideLeft x .plus .plus .minus .minus .minus = insertionSlideRight x .plus .plus .minus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_15_0 (x : ℂ) :
    insertionSlideLeft x .plus .minus .zero .zero .zero = insertionSlideRight x .plus .minus .zero .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_15_1 (x : ℂ) :
    insertionSlideLeft x .plus .minus .zero .zero .plus = insertionSlideRight x .plus .minus .zero .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_15_2 (x : ℂ) :
    insertionSlideLeft x .plus .minus .zero .zero .minus = insertionSlideRight x .plus .minus .zero .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_15_3 (x : ℂ) :
    insertionSlideLeft x .plus .minus .zero .plus .zero = insertionSlideRight x .plus .minus .zero .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_15_4 (x : ℂ) :
    insertionSlideLeft x .plus .minus .zero .plus .plus = insertionSlideRight x .plus .minus .zero .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_15_5 (x : ℂ) :
    insertionSlideLeft x .plus .minus .zero .plus .minus = insertionSlideRight x .plus .minus .zero .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_15_6 (x : ℂ) :
    insertionSlideLeft x .plus .minus .zero .minus .zero = insertionSlideRight x .plus .minus .zero .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_15_7 (x : ℂ) :
    insertionSlideLeft x .plus .minus .zero .minus .plus = insertionSlideRight x .plus .minus .zero .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_15_8 (x : ℂ) :
    insertionSlideLeft x .plus .minus .zero .minus .minus = insertionSlideRight x .plus .minus .zero .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_16_0 (x : ℂ) :
    insertionSlideLeft x .plus .minus .plus .zero .zero = insertionSlideRight x .plus .minus .plus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_16_1 (x : ℂ) :
    insertionSlideLeft x .plus .minus .plus .zero .plus = insertionSlideRight x .plus .minus .plus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_16_2 (x : ℂ) :
    insertionSlideLeft x .plus .minus .plus .zero .minus = insertionSlideRight x .plus .minus .plus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_16_3 (x : ℂ) :
    insertionSlideLeft x .plus .minus .plus .plus .zero = insertionSlideRight x .plus .minus .plus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_16_4 (x : ℂ) :
    insertionSlideLeft x .plus .minus .plus .plus .plus = insertionSlideRight x .plus .minus .plus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_16_5 (x : ℂ) :
    insertionSlideLeft x .plus .minus .plus .plus .minus = insertionSlideRight x .plus .minus .plus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_16_6 (x : ℂ) :
    insertionSlideLeft x .plus .minus .plus .minus .zero = insertionSlideRight x .plus .minus .plus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_16_7 (x : ℂ) :
    insertionSlideLeft x .plus .minus .plus .minus .plus = insertionSlideRight x .plus .minus .plus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_16_8 (x : ℂ) :
    insertionSlideLeft x .plus .minus .plus .minus .minus = insertionSlideRight x .plus .minus .plus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_17_0 (x : ℂ) :
    insertionSlideLeft x .plus .minus .minus .zero .zero = insertionSlideRight x .plus .minus .minus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_17_1 (x : ℂ) :
    insertionSlideLeft x .plus .minus .minus .zero .plus = insertionSlideRight x .plus .minus .minus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_17_2 (x : ℂ) :
    insertionSlideLeft x .plus .minus .minus .zero .minus = insertionSlideRight x .plus .minus .minus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_17_3 (x : ℂ) :
    insertionSlideLeft x .plus .minus .minus .plus .zero = insertionSlideRight x .plus .minus .minus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_17_4 (x : ℂ) :
    insertionSlideLeft x .plus .minus .minus .plus .plus = insertionSlideRight x .plus .minus .minus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_17_5 (x : ℂ) :
    insertionSlideLeft x .plus .minus .minus .plus .minus = insertionSlideRight x .plus .minus .minus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_17_6 (x : ℂ) :
    insertionSlideLeft x .plus .minus .minus .minus .zero = insertionSlideRight x .plus .minus .minus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_17_7 (x : ℂ) :
    insertionSlideLeft x .plus .minus .minus .minus .plus = insertionSlideRight x .plus .minus .minus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_17_8 (x : ℂ) :
    insertionSlideLeft x .plus .minus .minus .minus .minus = insertionSlideRight x .plus .minus .minus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_18_0 (x : ℂ) :
    insertionSlideLeft x .minus .zero .zero .zero .zero = insertionSlideRight x .minus .zero .zero .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_18_1 (x : ℂ) :
    insertionSlideLeft x .minus .zero .zero .zero .plus = insertionSlideRight x .minus .zero .zero .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_18_2 (x : ℂ) :
    insertionSlideLeft x .minus .zero .zero .zero .minus = insertionSlideRight x .minus .zero .zero .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_18_3 (x : ℂ) :
    insertionSlideLeft x .minus .zero .zero .plus .zero = insertionSlideRight x .minus .zero .zero .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_18_4 (x : ℂ) :
    insertionSlideLeft x .minus .zero .zero .plus .plus = insertionSlideRight x .minus .zero .zero .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_18_5 (x : ℂ) :
    insertionSlideLeft x .minus .zero .zero .plus .minus = insertionSlideRight x .minus .zero .zero .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_18_6 (x : ℂ) :
    insertionSlideLeft x .minus .zero .zero .minus .zero = insertionSlideRight x .minus .zero .zero .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_18_7 (x : ℂ) :
    insertionSlideLeft x .minus .zero .zero .minus .plus = insertionSlideRight x .minus .zero .zero .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_18_8 (x : ℂ) :
    insertionSlideLeft x .minus .zero .zero .minus .minus = insertionSlideRight x .minus .zero .zero .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_19_0 (x : ℂ) :
    insertionSlideLeft x .minus .zero .plus .zero .zero = insertionSlideRight x .minus .zero .plus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_19_1 (x : ℂ) :
    insertionSlideLeft x .minus .zero .plus .zero .plus = insertionSlideRight x .minus .zero .plus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_19_2 (x : ℂ) :
    insertionSlideLeft x .minus .zero .plus .zero .minus = insertionSlideRight x .minus .zero .plus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_19_3 (x : ℂ) :
    insertionSlideLeft x .minus .zero .plus .plus .zero = insertionSlideRight x .minus .zero .plus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_19_4 (x : ℂ) :
    insertionSlideLeft x .minus .zero .plus .plus .plus = insertionSlideRight x .minus .zero .plus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_19_5 (x : ℂ) :
    insertionSlideLeft x .minus .zero .plus .plus .minus = insertionSlideRight x .minus .zero .plus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_19_6 (x : ℂ) :
    insertionSlideLeft x .minus .zero .plus .minus .zero = insertionSlideRight x .minus .zero .plus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_19_7 (x : ℂ) :
    insertionSlideLeft x .minus .zero .plus .minus .plus = insertionSlideRight x .minus .zero .plus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_19_8 (x : ℂ) :
    insertionSlideLeft x .minus .zero .plus .minus .minus = insertionSlideRight x .minus .zero .plus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_20_0 (x : ℂ) :
    insertionSlideLeft x .minus .zero .minus .zero .zero = insertionSlideRight x .minus .zero .minus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_20_1 (x : ℂ) :
    insertionSlideLeft x .minus .zero .minus .zero .plus = insertionSlideRight x .minus .zero .minus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_20_2 (x : ℂ) :
    insertionSlideLeft x .minus .zero .minus .zero .minus = insertionSlideRight x .minus .zero .minus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_20_3 (x : ℂ) :
    insertionSlideLeft x .minus .zero .minus .plus .zero = insertionSlideRight x .minus .zero .minus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_20_4 (x : ℂ) :
    insertionSlideLeft x .minus .zero .minus .plus .plus = insertionSlideRight x .minus .zero .minus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_20_5 (x : ℂ) :
    insertionSlideLeft x .minus .zero .minus .plus .minus = insertionSlideRight x .minus .zero .minus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_20_6 (x : ℂ) :
    insertionSlideLeft x .minus .zero .minus .minus .zero = insertionSlideRight x .minus .zero .minus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_20_7 (x : ℂ) :
    insertionSlideLeft x .minus .zero .minus .minus .plus = insertionSlideRight x .minus .zero .minus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_20_8 (x : ℂ) :
    insertionSlideLeft x .minus .zero .minus .minus .minus = insertionSlideRight x .minus .zero .minus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_21_0 (x : ℂ) :
    insertionSlideLeft x .minus .plus .zero .zero .zero = insertionSlideRight x .minus .plus .zero .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_21_1 (x : ℂ) :
    insertionSlideLeft x .minus .plus .zero .zero .plus = insertionSlideRight x .minus .plus .zero .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_21_2 (x : ℂ) :
    insertionSlideLeft x .minus .plus .zero .zero .minus = insertionSlideRight x .minus .plus .zero .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_21_3 (x : ℂ) :
    insertionSlideLeft x .minus .plus .zero .plus .zero = insertionSlideRight x .minus .plus .zero .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_21_4 (x : ℂ) :
    insertionSlideLeft x .minus .plus .zero .plus .plus = insertionSlideRight x .minus .plus .zero .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_21_5 (x : ℂ) :
    insertionSlideLeft x .minus .plus .zero .plus .minus = insertionSlideRight x .minus .plus .zero .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_21_6 (x : ℂ) :
    insertionSlideLeft x .minus .plus .zero .minus .zero = insertionSlideRight x .minus .plus .zero .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_21_7 (x : ℂ) :
    insertionSlideLeft x .minus .plus .zero .minus .plus = insertionSlideRight x .minus .plus .zero .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_21_8 (x : ℂ) :
    insertionSlideLeft x .minus .plus .zero .minus .minus = insertionSlideRight x .minus .plus .zero .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_22_0 (x : ℂ) :
    insertionSlideLeft x .minus .plus .plus .zero .zero = insertionSlideRight x .minus .plus .plus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_22_1 (x : ℂ) :
    insertionSlideLeft x .minus .plus .plus .zero .plus = insertionSlideRight x .minus .plus .plus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_22_2 (x : ℂ) :
    insertionSlideLeft x .minus .plus .plus .zero .minus = insertionSlideRight x .minus .plus .plus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_22_3 (x : ℂ) :
    insertionSlideLeft x .minus .plus .plus .plus .zero = insertionSlideRight x .minus .plus .plus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_22_4 (x : ℂ) :
    insertionSlideLeft x .minus .plus .plus .plus .plus = insertionSlideRight x .minus .plus .plus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_22_5 (x : ℂ) :
    insertionSlideLeft x .minus .plus .plus .plus .minus = insertionSlideRight x .minus .plus .plus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_22_6 (x : ℂ) :
    insertionSlideLeft x .minus .plus .plus .minus .zero = insertionSlideRight x .minus .plus .plus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_22_7 (x : ℂ) :
    insertionSlideLeft x .minus .plus .plus .minus .plus = insertionSlideRight x .minus .plus .plus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_22_8 (x : ℂ) :
    insertionSlideLeft x .minus .plus .plus .minus .minus = insertionSlideRight x .minus .plus .plus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_23_0 (x : ℂ) :
    insertionSlideLeft x .minus .plus .minus .zero .zero = insertionSlideRight x .minus .plus .minus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_23_1 (x : ℂ) :
    insertionSlideLeft x .minus .plus .minus .zero .plus = insertionSlideRight x .minus .plus .minus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_23_2 (x : ℂ) :
    insertionSlideLeft x .minus .plus .minus .zero .minus = insertionSlideRight x .minus .plus .minus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_23_3 (x : ℂ) :
    insertionSlideLeft x .minus .plus .minus .plus .zero = insertionSlideRight x .minus .plus .minus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_23_4 (x : ℂ) :
    insertionSlideLeft x .minus .plus .minus .plus .plus = insertionSlideRight x .minus .plus .minus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_23_5 (x : ℂ) :
    insertionSlideLeft x .minus .plus .minus .plus .minus = insertionSlideRight x .minus .plus .minus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_23_6 (x : ℂ) :
    insertionSlideLeft x .minus .plus .minus .minus .zero = insertionSlideRight x .minus .plus .minus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_23_7 (x : ℂ) :
    insertionSlideLeft x .minus .plus .minus .minus .plus = insertionSlideRight x .minus .plus .minus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_23_8 (x : ℂ) :
    insertionSlideLeft x .minus .plus .minus .minus .minus = insertionSlideRight x .minus .plus .minus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_24_0 (x : ℂ) :
    insertionSlideLeft x .minus .minus .zero .zero .zero = insertionSlideRight x .minus .minus .zero .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_24_1 (x : ℂ) :
    insertionSlideLeft x .minus .minus .zero .zero .plus = insertionSlideRight x .minus .minus .zero .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_24_2 (x : ℂ) :
    insertionSlideLeft x .minus .minus .zero .zero .minus = insertionSlideRight x .minus .minus .zero .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_24_3 (x : ℂ) :
    insertionSlideLeft x .minus .minus .zero .plus .zero = insertionSlideRight x .minus .minus .zero .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_24_4 (x : ℂ) :
    insertionSlideLeft x .minus .minus .zero .plus .plus = insertionSlideRight x .minus .minus .zero .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_24_5 (x : ℂ) :
    insertionSlideLeft x .minus .minus .zero .plus .minus = insertionSlideRight x .minus .minus .zero .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_24_6 (x : ℂ) :
    insertionSlideLeft x .minus .minus .zero .minus .zero = insertionSlideRight x .minus .minus .zero .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_24_7 (x : ℂ) :
    insertionSlideLeft x .minus .minus .zero .minus .plus = insertionSlideRight x .minus .minus .zero .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_24_8 (x : ℂ) :
    insertionSlideLeft x .minus .minus .zero .minus .minus = insertionSlideRight x .minus .minus .zero .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_25_0 (x : ℂ) :
    insertionSlideLeft x .minus .minus .plus .zero .zero = insertionSlideRight x .minus .minus .plus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_25_1 (x : ℂ) :
    insertionSlideLeft x .minus .minus .plus .zero .plus = insertionSlideRight x .minus .minus .plus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_25_2 (x : ℂ) :
    insertionSlideLeft x .minus .minus .plus .zero .minus = insertionSlideRight x .minus .minus .plus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_25_3 (x : ℂ) :
    insertionSlideLeft x .minus .minus .plus .plus .zero = insertionSlideRight x .minus .minus .plus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_25_4 (x : ℂ) :
    insertionSlideLeft x .minus .minus .plus .plus .plus = insertionSlideRight x .minus .minus .plus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_25_5 (x : ℂ) :
    insertionSlideLeft x .minus .minus .plus .plus .minus = insertionSlideRight x .minus .minus .plus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_25_6 (x : ℂ) :
    insertionSlideLeft x .minus .minus .plus .minus .zero = insertionSlideRight x .minus .minus .plus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]
  all_goals vacuum_ring_finish

theorem insertion_slide_entry_25_7 (x : ℂ) :
    insertionSlideLeft x .minus .minus .plus .minus .plus = insertionSlideRight x .minus .minus .plus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_25_8 (x : ℂ) :
    insertionSlideLeft x .minus .minus .plus .minus .minus = insertionSlideRight x .minus .minus .plus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_26_0 (x : ℂ) :
    insertionSlideLeft x .minus .minus .minus .zero .zero = insertionSlideRight x .minus .minus .minus .zero .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_26_1 (x : ℂ) :
    insertionSlideLeft x .minus .minus .minus .zero .plus = insertionSlideRight x .minus .minus .minus .zero .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_26_2 (x : ℂ) :
    insertionSlideLeft x .minus .minus .minus .zero .minus = insertionSlideRight x .minus .minus .minus .zero .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_26_3 (x : ℂ) :
    insertionSlideLeft x .minus .minus .minus .plus .zero = insertionSlideRight x .minus .minus .minus .plus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_26_4 (x : ℂ) :
    insertionSlideLeft x .minus .minus .minus .plus .plus = insertionSlideRight x .minus .minus .minus .plus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_26_5 (x : ℂ) :
    insertionSlideLeft x .minus .minus .minus .plus .minus = insertionSlideRight x .minus .minus .minus .plus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_26_6 (x : ℂ) :
    insertionSlideLeft x .minus .minus .minus .minus .zero = insertionSlideRight x .minus .minus .minus .minus .zero := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_26_7 (x : ℂ) :
    insertionSlideLeft x .minus .minus .minus .minus .plus = insertionSlideRight x .minus .minus .minus .minus .plus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_entry_26_8 (x : ℂ) :
    insertionSlideLeft x .minus .minus .minus .minus .minus = insertionSlideRight x .minus .minus .minus .minus .minus := by
  norm_num [insertionSlideLeft,insertionSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,insertion_eq_table,insertionTable,T,t]

theorem insertion_slide_coefficients (x : ℂ) (a b c h k : Spin) :
    insertionSlideLeft x a b c h k = insertionSlideRight x a b c h k := by
  cases a <;> cases b <;> cases c <;> cases h <;> cases k
  · exact insertion_slide_entry_0_0 x
  · exact insertion_slide_entry_0_1 x
  · exact insertion_slide_entry_0_2 x
  · exact insertion_slide_entry_0_3 x
  · exact insertion_slide_entry_0_4 x
  · exact insertion_slide_entry_0_5 x
  · exact insertion_slide_entry_0_6 x
  · exact insertion_slide_entry_0_7 x
  · exact insertion_slide_entry_0_8 x
  · exact insertion_slide_entry_1_0 x
  · exact insertion_slide_entry_1_1 x
  · exact insertion_slide_entry_1_2 x
  · exact insertion_slide_entry_1_3 x
  · exact insertion_slide_entry_1_4 x
  · exact insertion_slide_entry_1_5 x
  · exact insertion_slide_entry_1_6 x
  · exact insertion_slide_entry_1_7 x
  · exact insertion_slide_entry_1_8 x
  · exact insertion_slide_entry_2_0 x
  · exact insertion_slide_entry_2_1 x
  · exact insertion_slide_entry_2_2 x
  · exact insertion_slide_entry_2_3 x
  · exact insertion_slide_entry_2_4 x
  · exact insertion_slide_entry_2_5 x
  · exact insertion_slide_entry_2_6 x
  · exact insertion_slide_entry_2_7 x
  · exact insertion_slide_entry_2_8 x
  · exact insertion_slide_entry_3_0 x
  · exact insertion_slide_entry_3_1 x
  · exact insertion_slide_entry_3_2 x
  · exact insertion_slide_entry_3_3 x
  · exact insertion_slide_entry_3_4 x
  · exact insertion_slide_entry_3_5 x
  · exact insertion_slide_entry_3_6 x
  · exact insertion_slide_entry_3_7 x
  · exact insertion_slide_entry_3_8 x
  · exact insertion_slide_entry_4_0 x
  · exact insertion_slide_entry_4_1 x
  · exact insertion_slide_entry_4_2 x
  · exact insertion_slide_entry_4_3 x
  · exact insertion_slide_entry_4_4 x
  · exact insertion_slide_entry_4_5 x
  · exact insertion_slide_entry_4_6 x
  · exact insertion_slide_entry_4_7 x
  · exact insertion_slide_entry_4_8 x
  · exact insertion_slide_entry_5_0 x
  · exact insertion_slide_entry_5_1 x
  · exact insertion_slide_entry_5_2 x
  · exact insertion_slide_entry_5_3 x
  · exact insertion_slide_entry_5_4 x
  · exact insertion_slide_entry_5_5 x
  · exact insertion_slide_entry_5_6 x
  · exact insertion_slide_entry_5_7 x
  · exact insertion_slide_entry_5_8 x
  · exact insertion_slide_entry_6_0 x
  · exact insertion_slide_entry_6_1 x
  · exact insertion_slide_entry_6_2 x
  · exact insertion_slide_entry_6_3 x
  · exact insertion_slide_entry_6_4 x
  · exact insertion_slide_entry_6_5 x
  · exact insertion_slide_entry_6_6 x
  · exact insertion_slide_entry_6_7 x
  · exact insertion_slide_entry_6_8 x
  · exact insertion_slide_entry_7_0 x
  · exact insertion_slide_entry_7_1 x
  · exact insertion_slide_entry_7_2 x
  · exact insertion_slide_entry_7_3 x
  · exact insertion_slide_entry_7_4 x
  · exact insertion_slide_entry_7_5 x
  · exact insertion_slide_entry_7_6 x
  · exact insertion_slide_entry_7_7 x
  · exact insertion_slide_entry_7_8 x
  · exact insertion_slide_entry_8_0 x
  · exact insertion_slide_entry_8_1 x
  · exact insertion_slide_entry_8_2 x
  · exact insertion_slide_entry_8_3 x
  · exact insertion_slide_entry_8_4 x
  · exact insertion_slide_entry_8_5 x
  · exact insertion_slide_entry_8_6 x
  · exact insertion_slide_entry_8_7 x
  · exact insertion_slide_entry_8_8 x
  · exact insertion_slide_entry_9_0 x
  · exact insertion_slide_entry_9_1 x
  · exact insertion_slide_entry_9_2 x
  · exact insertion_slide_entry_9_3 x
  · exact insertion_slide_entry_9_4 x
  · exact insertion_slide_entry_9_5 x
  · exact insertion_slide_entry_9_6 x
  · exact insertion_slide_entry_9_7 x
  · exact insertion_slide_entry_9_8 x
  · exact insertion_slide_entry_10_0 x
  · exact insertion_slide_entry_10_1 x
  · exact insertion_slide_entry_10_2 x
  · exact insertion_slide_entry_10_3 x
  · exact insertion_slide_entry_10_4 x
  · exact insertion_slide_entry_10_5 x
  · exact insertion_slide_entry_10_6 x
  · exact insertion_slide_entry_10_7 x
  · exact insertion_slide_entry_10_8 x
  · exact insertion_slide_entry_11_0 x
  · exact insertion_slide_entry_11_1 x
  · exact insertion_slide_entry_11_2 x
  · exact insertion_slide_entry_11_3 x
  · exact insertion_slide_entry_11_4 x
  · exact insertion_slide_entry_11_5 x
  · exact insertion_slide_entry_11_6 x
  · exact insertion_slide_entry_11_7 x
  · exact insertion_slide_entry_11_8 x
  · exact insertion_slide_entry_12_0 x
  · exact insertion_slide_entry_12_1 x
  · exact insertion_slide_entry_12_2 x
  · exact insertion_slide_entry_12_3 x
  · exact insertion_slide_entry_12_4 x
  · exact insertion_slide_entry_12_5 x
  · exact insertion_slide_entry_12_6 x
  · exact insertion_slide_entry_12_7 x
  · exact insertion_slide_entry_12_8 x
  · exact insertion_slide_entry_13_0 x
  · exact insertion_slide_entry_13_1 x
  · exact insertion_slide_entry_13_2 x
  · exact insertion_slide_entry_13_3 x
  · exact insertion_slide_entry_13_4 x
  · exact insertion_slide_entry_13_5 x
  · exact insertion_slide_entry_13_6 x
  · exact insertion_slide_entry_13_7 x
  · exact insertion_slide_entry_13_8 x
  · exact insertion_slide_entry_14_0 x
  · exact insertion_slide_entry_14_1 x
  · exact insertion_slide_entry_14_2 x
  · exact insertion_slide_entry_14_3 x
  · exact insertion_slide_entry_14_4 x
  · exact insertion_slide_entry_14_5 x
  · exact insertion_slide_entry_14_6 x
  · exact insertion_slide_entry_14_7 x
  · exact insertion_slide_entry_14_8 x
  · exact insertion_slide_entry_15_0 x
  · exact insertion_slide_entry_15_1 x
  · exact insertion_slide_entry_15_2 x
  · exact insertion_slide_entry_15_3 x
  · exact insertion_slide_entry_15_4 x
  · exact insertion_slide_entry_15_5 x
  · exact insertion_slide_entry_15_6 x
  · exact insertion_slide_entry_15_7 x
  · exact insertion_slide_entry_15_8 x
  · exact insertion_slide_entry_16_0 x
  · exact insertion_slide_entry_16_1 x
  · exact insertion_slide_entry_16_2 x
  · exact insertion_slide_entry_16_3 x
  · exact insertion_slide_entry_16_4 x
  · exact insertion_slide_entry_16_5 x
  · exact insertion_slide_entry_16_6 x
  · exact insertion_slide_entry_16_7 x
  · exact insertion_slide_entry_16_8 x
  · exact insertion_slide_entry_17_0 x
  · exact insertion_slide_entry_17_1 x
  · exact insertion_slide_entry_17_2 x
  · exact insertion_slide_entry_17_3 x
  · exact insertion_slide_entry_17_4 x
  · exact insertion_slide_entry_17_5 x
  · exact insertion_slide_entry_17_6 x
  · exact insertion_slide_entry_17_7 x
  · exact insertion_slide_entry_17_8 x
  · exact insertion_slide_entry_18_0 x
  · exact insertion_slide_entry_18_1 x
  · exact insertion_slide_entry_18_2 x
  · exact insertion_slide_entry_18_3 x
  · exact insertion_slide_entry_18_4 x
  · exact insertion_slide_entry_18_5 x
  · exact insertion_slide_entry_18_6 x
  · exact insertion_slide_entry_18_7 x
  · exact insertion_slide_entry_18_8 x
  · exact insertion_slide_entry_19_0 x
  · exact insertion_slide_entry_19_1 x
  · exact insertion_slide_entry_19_2 x
  · exact insertion_slide_entry_19_3 x
  · exact insertion_slide_entry_19_4 x
  · exact insertion_slide_entry_19_5 x
  · exact insertion_slide_entry_19_6 x
  · exact insertion_slide_entry_19_7 x
  · exact insertion_slide_entry_19_8 x
  · exact insertion_slide_entry_20_0 x
  · exact insertion_slide_entry_20_1 x
  · exact insertion_slide_entry_20_2 x
  · exact insertion_slide_entry_20_3 x
  · exact insertion_slide_entry_20_4 x
  · exact insertion_slide_entry_20_5 x
  · exact insertion_slide_entry_20_6 x
  · exact insertion_slide_entry_20_7 x
  · exact insertion_slide_entry_20_8 x
  · exact insertion_slide_entry_21_0 x
  · exact insertion_slide_entry_21_1 x
  · exact insertion_slide_entry_21_2 x
  · exact insertion_slide_entry_21_3 x
  · exact insertion_slide_entry_21_4 x
  · exact insertion_slide_entry_21_5 x
  · exact insertion_slide_entry_21_6 x
  · exact insertion_slide_entry_21_7 x
  · exact insertion_slide_entry_21_8 x
  · exact insertion_slide_entry_22_0 x
  · exact insertion_slide_entry_22_1 x
  · exact insertion_slide_entry_22_2 x
  · exact insertion_slide_entry_22_3 x
  · exact insertion_slide_entry_22_4 x
  · exact insertion_slide_entry_22_5 x
  · exact insertion_slide_entry_22_6 x
  · exact insertion_slide_entry_22_7 x
  · exact insertion_slide_entry_22_8 x
  · exact insertion_slide_entry_23_0 x
  · exact insertion_slide_entry_23_1 x
  · exact insertion_slide_entry_23_2 x
  · exact insertion_slide_entry_23_3 x
  · exact insertion_slide_entry_23_4 x
  · exact insertion_slide_entry_23_5 x
  · exact insertion_slide_entry_23_6 x
  · exact insertion_slide_entry_23_7 x
  · exact insertion_slide_entry_23_8 x
  · exact insertion_slide_entry_24_0 x
  · exact insertion_slide_entry_24_1 x
  · exact insertion_slide_entry_24_2 x
  · exact insertion_slide_entry_24_3 x
  · exact insertion_slide_entry_24_4 x
  · exact insertion_slide_entry_24_5 x
  · exact insertion_slide_entry_24_6 x
  · exact insertion_slide_entry_24_7 x
  · exact insertion_slide_entry_24_8 x
  · exact insertion_slide_entry_25_0 x
  · exact insertion_slide_entry_25_1 x
  · exact insertion_slide_entry_25_2 x
  · exact insertion_slide_entry_25_3 x
  · exact insertion_slide_entry_25_4 x
  · exact insertion_slide_entry_25_5 x
  · exact insertion_slide_entry_25_6 x
  · exact insertion_slide_entry_25_7 x
  · exact insertion_slide_entry_25_8 x
  · exact insertion_slide_entry_26_0 x
  · exact insertion_slide_entry_26_1 x
  · exact insertion_slide_entry_26_2 x
  · exact insertion_slide_entry_26_3 x
  · exact insertion_slide_entry_26_4 x
  · exact insertion_slide_entry_26_5 x
  · exact insertion_slide_entry_26_6 x
  · exact insertion_slide_entry_26_7 x
  · exact insertion_slide_entry_26_8 x

end PolynomialVacuumAlgebra

end OAI
