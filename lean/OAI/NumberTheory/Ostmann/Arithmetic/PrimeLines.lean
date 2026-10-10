import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeLines
open scoped BigOperators

variable {K : Type*} [Field K]

def mixedLineEquiv (a b : K) (ha : a ≠ 0) :
    {z : K × Kˣ // a*z.1 + b*(z.2 : K) = 0} ≃ Kˣ where
  toFun z := z.val.2
  invFun y := ⟨((-b*(y:K))/a,y), by dsimp; field_simp; ring⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      apply (div_eq_iff ha).2
      linear_combination -z.property
    · rfl
  right_inv _ := rfl

def unitLineEquiv (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    {z : Kˣ × Kˣ // a*(z.1 : K) + b*(z.2 : K) = 0} ≃ Kˣ where
  toFun z := z.val.2
  invFun y := ⟨(Units.mk0 ((-b*(y:K))/a)
    (div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hb) (Units.ne_zero y)) ha), y), by
      dsimp; field_simp; ring⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Units.ext
      dsimp
      apply (div_eq_iff ha).2
      linear_combination -z.property
    · rfl
  right_inv _ := rfl

theorem rank_two_impossible (a b c d x y : K)
    (hdet : a*d-b*c ≠ 0) (hy : y ≠ 0)
    (h₁ : a*x+b*y=0) (h₂ : c*x+d*y=0) : False := by
  have h : (a*d-b*c)*y=0 := by linear_combination a*h₂-c*h₁
  exact (mul_ne_zero hdet hy) h

theorem no_unit_solution_of_zero_coefficient {a b : K} (ha : a = 0) (hb : b ≠ 0)
    (x y : Kˣ) : a*(x:K)+b*(y:K) ≠ 0 := by
  simp only [ha, zero_mul, zero_add]
  exact mul_ne_zero hb (Units.ne_zero y)

theorem card_mixed_line [Fintype K] [DecidableEq K] (a b : K) (ha : a ≠ 0) :
    Nat.card {z : K × Kˣ // a*z.1+b*(z.2:K)=0} = Fintype.card Kˣ := by
  rw [Nat.card_congr (mixedLineEquiv a b ha), Nat.card_eq_fintype_card]

theorem card_unit_line [Fintype K] [DecidableEq K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.card {z : Kˣ × Kˣ // a*(z.1:K)+b*(z.2:K)=0} = Fintype.card Kˣ := by
  rw [Nat.card_congr (unitLineEquiv a b ha hb), Nat.card_eq_fintype_card]

theorem prime_mixed_probability (p : ℕ) [Fact p.Prime]
    (a b : ZMod p) (ha : a ≠ 0) :
    (Nat.card {z : ZMod p × (ZMod p)ˣ // a*z.1+b*(z.2:ZMod p)=0} : ℝ) /
      Fintype.card (ZMod p × (ZMod p)ˣ) = (p:ℝ)⁻¹ := by
  rw [card_mixed_line a b ha, Fintype.card_prod, ZMod.card, ZMod.card_units]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : 0 < p-1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  push_cast
  field_simp

theorem prime_unit_probability (p : ℕ) [Fact p.Prime]
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.card {z : (ZMod p)ˣ × (ZMod p)ˣ // a*(z.1:ZMod p)+b*(z.2:ZMod p)=0} : ℝ) /
      Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ) = ((p-1:ℕ):ℝ)⁻¹ := by
  rw [card_unit_line a b ha hb, Fintype.card_prod, ZMod.card_units]
  have hp1 : 0 < p-1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  push_cast
  field_simp

end Ostmann.Arithmetic.PrimeLines

end

end OAI
