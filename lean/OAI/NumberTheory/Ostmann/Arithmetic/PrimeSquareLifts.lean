import OAI.NumberTheory.Ostmann.Arithmetic.PrimeLines

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeSquareLifts

theorem square_divides_lift_iff {p a b x y k u v : ℤ} (hp : p ≠ 0)
    (hbase : a*x+b*y=p*k) :
    p*p ∣ a*(x+p*u)+b*(y+p*v) ↔ p ∣ k+a*u+b*v := by
  have heq : a*(x+p*u)+b*(y+p*v)=p*(k+a*u+b*v) := by
    linear_combination hbase
  rw [heq, mul_dvd_mul_iff_left hp]

def affineLineEquiv {K : Type*} [Field K] (a b c : K) (ha : a ≠ 0) :
    {z : K × K // a*z.1+b*z.2=c} ≃ K where
  toFun z := z.val.2
  invFun y := ⟨((c-b*y)/a,y), by dsimp; field_simp; ring⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      apply (div_eq_iff ha).2
      linear_combination -z.property
    · rfl
  right_inv _ := rfl

theorem prime_lift_probability (p : ℕ) [Fact p.Prime]
    (a b c : ZMod p) (ha : a ≠ 0) :
    (Nat.card {z : ZMod p × ZMod p // a*z.1+b*z.2=c} : ℝ) /
      Fintype.card (ZMod p × ZMod p) = (p:ℝ)⁻¹ := by
  rw [Nat.card_congr (affineLineEquiv a b c ha), Nat.card_eq_fintype_card,
    Fintype.card_prod, ZMod.card]
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  push_cast
  field_simp

theorem square_divides_lift_iff_residue (p : ℕ) [Fact p.Prime]
    (a b x y k u v : ℤ) (hbase : a*x+b*y=(p:ℤ)*k) :
    (p:ℤ)*(p:ℤ) ∣ a*(x+(p:ℤ)*u)+b*(y+(p:ℤ)*v) ↔
      (a:ZMod p)*(u:ZMod p)+(b:ZMod p)*(v:ZMod p)=-(k:ZMod p) := by
  rw [square_divides_lift_iff (by exact_mod_cast (Fact.out : p.Prime).ne_zero) hbase]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  constructor <;> intro h <;> linear_combination h

end Ostmann.Arithmetic.PrimeSquareLifts

end

end OAI
