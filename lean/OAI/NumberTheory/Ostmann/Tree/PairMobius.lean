import Mathlib

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
variable {F : Type*} [Field F]

abbrev NonzeroExcept (F : Type*) [Field F] (c : F) := {x : F // x ≠ 0 ∧ x ≠ c}

def pairMobiusValue (c : Fˣ) (t : F) : F := (c:F)*t/(t-1)

theorem pairMobiusValue_sub (c : Fˣ) (t : F) (ht : t ≠ 1) :
    pairMobiusValue c t-(c:F) = (c:F)/(t-1) := by
  dsimp [pairMobiusValue]
  field_simp
  ring

def pairMobius (c : Fˣ) : NonzeroExcept F 1 ≃ NonzeroExcept F (c:F) where
  toFun t := ⟨pairMobiusValue c t, by
    refine ⟨div_ne_zero (mul_ne_zero (Units.ne_zero c) t.property.1)
      (sub_ne_zero.mpr t.property.2), ?_⟩
    intro h
    have he := pairMobiusValue_sub c t t.property.2
    rw [h, sub_self] at he
    exact div_ne_zero (Units.ne_zero c) (sub_ne_zero.mpr t.property.2) he.symm⟩
  invFun x := ⟨(x:F)/((x:F)-(c:F)), by
    have hx := sub_ne_zero.mpr x.property.2
    refine ⟨div_ne_zero x.property.1 hx, ?_⟩
    intro h
    have he := (div_eq_one_iff_eq hx).mp h
    exact Units.ne_zero c (by linear_combination he)⟩
  left_inv t := by
    apply Subtype.ext
    dsimp
    rw [pairMobiusValue_sub c t t.property.2]
    dsimp [pairMobiusValue]
    have ht := sub_ne_zero.mpr t.property.2
    field_simp
  right_inv x := by
    apply Subtype.ext
    dsimp [pairMobiusValue]
    have hx := sub_ne_zero.mpr x.property.2
    field_simp
    ring

section Sums
open scoped BigOperators
variable [Fintype F] [DecidableEq F]

theorem sum_nonzeroExcept_of_zero (c : F) (g : F → ℂ) (h0 : g 0=0) (hc : g c=0) :
    ∑ x : NonzeroExcept F c, g x = ∑ x : F, g x := by
  apply Fintype.sum_of_injective (fun x : NonzeroExcept F c => (x:F)) Subtype.val_injective
  · intro x hx
    by_cases hzero : x=0
    · simpa only [hzero] using h0
    by_cases heq : x=c
    · simpa only [heq] using hc
    exact False.elim (hx ⟨⟨x,hzero,heq⟩,rfl⟩)
  · intro _
    rfl

theorem pairMobius_sum (c : Fˣ) (g : F → ℂ) (h0 : g 0=0) (hc : g c=0) :
    ∑ t : F, g (pairMobiusValue c t) = ∑ x : F, g x := by
  have hs : (∑ t : F, g (pairMobiusValue c t)) =
      ∑ t : NonzeroExcept F 1, g (pairMobiusValue c t) := by
    apply (sum_nonzeroExcept_of_zero 1 _ _ _).symm
    · simpa only [pairMobiusValue, mul_zero, zero_div] using h0
    · simpa only [pairMobiusValue, sub_self, div_zero] using h0
  rw [hs]
  calc
    _ = ∑ x : NonzeroExcept F (c:F), g x :=
      (pairMobius c).bijective.sum_comp (fun x : NonzeroExcept F (c:F) => g x)
    _ = _ := sum_nonzeroExcept_of_zero (c:F) g h0 hc

end Sums
end
end Ostmann.FiniteField

end OAI
