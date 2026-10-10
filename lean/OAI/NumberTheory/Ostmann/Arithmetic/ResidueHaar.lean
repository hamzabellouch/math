import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.ResidueHaar
open scoped BigOperators

def average {α : Type*} [Fintype α] (f : α → ℂ) : ℂ :=
  (Fintype.card α : ℂ)⁻¹ * ∑ x, f x

theorem average_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℂ) : average (fun x => f (e x)) = average f := by
  unfold average
  rw [Fintype.card_congr e, e.sum_comp]

theorem average_product {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ) :
    average (fun z : α × β => f z.1 * g z.2) = average f * average g := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

def crtUnits {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

theorem crt_average_product {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (f : (ZMod m)ˣ → ℂ) (g : (ZMod n)ˣ → ℂ) :
    average (fun z : (ZMod (m*n))ˣ =>
      f (crtUnits h z).1 * g (crtUnits h z).2) = average f * average g := by
  exact (average_equiv (crtUnits h).toEquiv
    (fun z => f z.1 * g z.2)).trans (average_product f g)

def splitEquiv {G : Type*} [Group G] : G × G ≃ G × G where
  toFun z := (z.1*z.2,z.1)
  invFun z := (z.2,z.2⁻¹*z.1)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp

theorem split_average {G : Type*} [Group G] [Fintype G]
    (F : G × G → ℂ) :
    average (fun z : G × G => F (z.1*z.2,z.1)) = average F :=
  average_equiv splitEquiv F

def fixedProductEquiv {G : Type*} [Group G] (t : G) :
    {z : G × G // z.1*z.2=t} ≃ G where
  toFun z := z.val.1
  invFun x := ⟨(x,x⁻¹*t), by simp⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      calc
        _ = (z.val.1)⁻¹ * (z.val.1*z.val.2) :=
          congrArg (fun w => (z.val.1)⁻¹*w) z.property.symm
        _ = _ := by simp
  right_inv _ := rfl

theorem fixedProduct_card {G : Type*} [Group G] [Finite G] (t : G) :
    Nat.card {z : G × G // z.1*z.2=t} = Nat.card G :=
  Nat.card_congr (fixedProductEquiv t)

end Ostmann.Arithmetic.ResidueHaar

end

end OAI
