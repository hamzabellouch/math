import OAI.Combinatorics.PolynomialVacuum.Algebra.CupPrescriptions

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

 
theorem exchange_top_carried (a b : Pair) (h : charge b.1 < charge a.2) :
    exchangeNumerator 1 0 a b=0 := by
  rcases a with ⟨a₁,a₂⟩
  rcases b with ⟨b₁,b₂⟩
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;>
    norm_num [charge] at h <;> norm_num [numerator_entry_0_0,numerator_entry_0_1,numerator_entry_0_2,numerator_entry_0_3,numerator_entry_0_4,numerator_entry_0_5,numerator_entry_0_6,numerator_entry_0_7,numerator_entry_0_8,numerator_entry_1_0,numerator_entry_1_1,numerator_entry_1_2,numerator_entry_1_3,numerator_entry_1_4,numerator_entry_1_5,numerator_entry_1_6,numerator_entry_1_7,numerator_entry_1_8,numerator_entry_2_0,numerator_entry_2_1,numerator_entry_2_2,numerator_entry_2_3,numerator_entry_2_4,numerator_entry_2_5,numerator_entry_2_6,numerator_entry_2_7,numerator_entry_2_8,numerator_entry_3_0,numerator_entry_3_1,numerator_entry_3_2,numerator_entry_3_3,numerator_entry_3_4,numerator_entry_3_5,numerator_entry_3_6,numerator_entry_3_7,numerator_entry_3_8,numerator_entry_4_0,numerator_entry_4_1,numerator_entry_4_2,numerator_entry_4_3,numerator_entry_4_4,numerator_entry_4_5,numerator_entry_4_6,numerator_entry_4_7,numerator_entry_4_8,numerator_entry_5_0,numerator_entry_5_1,numerator_entry_5_2,numerator_entry_5_3,numerator_entry_5_4,numerator_entry_5_5,numerator_entry_5_6,numerator_entry_5_7,numerator_entry_5_8,numerator_entry_6_0,numerator_entry_6_1,numerator_entry_6_2,numerator_entry_6_3,numerator_entry_6_4,numerator_entry_6_5,numerator_entry_6_6,numerator_entry_6_7,numerator_entry_6_8,numerator_entry_7_0,numerator_entry_7_1,numerator_entry_7_2,numerator_entry_7_3,numerator_entry_7_4,numerator_entry_7_5,numerator_entry_7_6,numerator_entry_7_7,numerator_entry_7_8,numerator_entry_8_0,numerator_entry_8_1,numerator_entry_8_2,numerator_entry_8_3,numerator_entry_8_4,numerator_entry_8_5,numerator_entry_8_6,numerator_entry_8_7,numerator_entry_8_8]

 
theorem exchange_top_spectator (a b : Pair) (h : charge b.2 < charge a.1) :
    exchangeNumerator 0 1 a b=0 := by
  rcases a with ⟨a₁,a₂⟩
  rcases b with ⟨b₁,b₂⟩
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;>
    norm_num [charge] at h <;> norm_num [numerator_entry_0_0,numerator_entry_0_1,numerator_entry_0_2,numerator_entry_0_3,numerator_entry_0_4,numerator_entry_0_5,numerator_entry_0_6,numerator_entry_0_7,numerator_entry_0_8,numerator_entry_1_0,numerator_entry_1_1,numerator_entry_1_2,numerator_entry_1_3,numerator_entry_1_4,numerator_entry_1_5,numerator_entry_1_6,numerator_entry_1_7,numerator_entry_1_8,numerator_entry_2_0,numerator_entry_2_1,numerator_entry_2_2,numerator_entry_2_3,numerator_entry_2_4,numerator_entry_2_5,numerator_entry_2_6,numerator_entry_2_7,numerator_entry_2_8,numerator_entry_3_0,numerator_entry_3_1,numerator_entry_3_2,numerator_entry_3_3,numerator_entry_3_4,numerator_entry_3_5,numerator_entry_3_6,numerator_entry_3_7,numerator_entry_3_8,numerator_entry_4_0,numerator_entry_4_1,numerator_entry_4_2,numerator_entry_4_3,numerator_entry_4_4,numerator_entry_4_5,numerator_entry_4_6,numerator_entry_4_7,numerator_entry_4_8,numerator_entry_5_0,numerator_entry_5_1,numerator_entry_5_2,numerator_entry_5_3,numerator_entry_5_4,numerator_entry_5_5,numerator_entry_5_6,numerator_entry_5_7,numerator_entry_5_8,numerator_entry_6_0,numerator_entry_6_1,numerator_entry_6_2,numerator_entry_6_3,numerator_entry_6_4,numerator_entry_6_5,numerator_entry_6_6,numerator_entry_6_7,numerator_entry_6_8,numerator_entry_7_0,numerator_entry_7_1,numerator_entry_7_2,numerator_entry_7_3,numerator_entry_7_4,numerator_entry_7_5,numerator_entry_7_6,numerator_entry_7_7,numerator_entry_7_8,numerator_entry_8_0,numerator_entry_8_1,numerator_entry_8_2,numerator_entry_8_3,numerator_entry_8_4,numerator_entry_8_5,numerator_entry_8_6,numerator_entry_8_7,numerator_entry_8_8]

 

theorem exchange_zero_carried (a b : Pair) (h : charge a.2 < charge b.1) :
    exchangeNumerator 0 1 a b=0 := by
  rcases a with ⟨a₁,a₂⟩
  rcases b with ⟨b₁,b₂⟩
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;>
    norm_num [charge] at h <;> norm_num [numerator_entry_0_0,numerator_entry_0_1,numerator_entry_0_2,numerator_entry_0_3,numerator_entry_0_4,numerator_entry_0_5,numerator_entry_0_6,numerator_entry_0_7,numerator_entry_0_8,numerator_entry_1_0,numerator_entry_1_1,numerator_entry_1_2,numerator_entry_1_3,numerator_entry_1_4,numerator_entry_1_5,numerator_entry_1_6,numerator_entry_1_7,numerator_entry_1_8,numerator_entry_2_0,numerator_entry_2_1,numerator_entry_2_2,numerator_entry_2_3,numerator_entry_2_4,numerator_entry_2_5,numerator_entry_2_6,numerator_entry_2_7,numerator_entry_2_8,numerator_entry_3_0,numerator_entry_3_1,numerator_entry_3_2,numerator_entry_3_3,numerator_entry_3_4,numerator_entry_3_5,numerator_entry_3_6,numerator_entry_3_7,numerator_entry_3_8,numerator_entry_4_0,numerator_entry_4_1,numerator_entry_4_2,numerator_entry_4_3,numerator_entry_4_4,numerator_entry_4_5,numerator_entry_4_6,numerator_entry_4_7,numerator_entry_4_8,numerator_entry_5_0,numerator_entry_5_1,numerator_entry_5_2,numerator_entry_5_3,numerator_entry_5_4,numerator_entry_5_5,numerator_entry_5_6,numerator_entry_5_7,numerator_entry_5_8,numerator_entry_6_0,numerator_entry_6_1,numerator_entry_6_2,numerator_entry_6_3,numerator_entry_6_4,numerator_entry_6_5,numerator_entry_6_6,numerator_entry_6_7,numerator_entry_6_8,numerator_entry_7_0,numerator_entry_7_1,numerator_entry_7_2,numerator_entry_7_3,numerator_entry_7_4,numerator_entry_7_5,numerator_entry_7_6,numerator_entry_7_7,numerator_entry_7_8,numerator_entry_8_0,numerator_entry_8_1,numerator_entry_8_2,numerator_entry_8_3,numerator_entry_8_4,numerator_entry_8_5,numerator_entry_8_6,numerator_entry_8_7,numerator_entry_8_8]

theorem exchange_zero_spectator (a b : Pair) (h : charge a.1 < charge b.2) :
    exchangeNumerator 1 0 a b=0 := by
  rcases a with ⟨a₁,a₂⟩
  rcases b with ⟨b₁,b₂⟩
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;>
    norm_num [charge] at h <;> norm_num [numerator_entry_0_0,numerator_entry_0_1,numerator_entry_0_2,numerator_entry_0_3,numerator_entry_0_4,numerator_entry_0_5,numerator_entry_0_6,numerator_entry_0_7,numerator_entry_0_8,numerator_entry_1_0,numerator_entry_1_1,numerator_entry_1_2,numerator_entry_1_3,numerator_entry_1_4,numerator_entry_1_5,numerator_entry_1_6,numerator_entry_1_7,numerator_entry_1_8,numerator_entry_2_0,numerator_entry_2_1,numerator_entry_2_2,numerator_entry_2_3,numerator_entry_2_4,numerator_entry_2_5,numerator_entry_2_6,numerator_entry_2_7,numerator_entry_2_8,numerator_entry_3_0,numerator_entry_3_1,numerator_entry_3_2,numerator_entry_3_3,numerator_entry_3_4,numerator_entry_3_5,numerator_entry_3_6,numerator_entry_3_7,numerator_entry_3_8,numerator_entry_4_0,numerator_entry_4_1,numerator_entry_4_2,numerator_entry_4_3,numerator_entry_4_4,numerator_entry_4_5,numerator_entry_4_6,numerator_entry_4_7,numerator_entry_4_8,numerator_entry_5_0,numerator_entry_5_1,numerator_entry_5_2,numerator_entry_5_3,numerator_entry_5_4,numerator_entry_5_5,numerator_entry_5_6,numerator_entry_5_7,numerator_entry_5_8,numerator_entry_6_0,numerator_entry_6_1,numerator_entry_6_2,numerator_entry_6_3,numerator_entry_6_4,numerator_entry_6_5,numerator_entry_6_6,numerator_entry_6_7,numerator_entry_6_8,numerator_entry_7_0,numerator_entry_7_1,numerator_entry_7_2,numerator_entry_7_3,numerator_entry_7_4,numerator_entry_7_5,numerator_entry_7_6,numerator_entry_7_7,numerator_entry_7_8,numerator_entry_8_0,numerator_entry_8_1,numerator_entry_8_2,numerator_entry_8_3,numerator_entry_8_4,numerator_entry_8_5,numerator_entry_8_6,numerator_entry_8_7,numerator_entry_8_8]

noncomputable def middleExchange (a b : Pair) : ℂ :=
  exchangeNumerator 1 1 a b-exchangeNumerator 1 0 a b-exchangeNumerator 0 1 a b

theorem polyExchange_split {ι : Type*} (x y : MvPolynomial ι ℂ) (a b : Pair) :
    polyExchangeNumerator x y a b=
      x^2*C (exchangeNumerator 1 0 a b)+x*y*C (middleExchange a b)+
        y^2*C (exchangeNumerator 0 1 a b) := by
  simp only [polyExchangeNumerator,middleExchange,exchangeNumerator,Matrix.add_apply,
    Matrix.smul_apply,smul_eq_mul,map_add,map_sub,map_mul,map_pow,map_one,map_zero]
  ring

end PolynomialVacuumAlgebra

end OAI
