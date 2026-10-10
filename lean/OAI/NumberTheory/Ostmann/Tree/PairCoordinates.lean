import Mathlib

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
variable {F : Type*} [Field F]

def PairInput (F : Type*) [Field F] := {v : F × F // v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ v.2 ≠ 1}

def PairOutput (F : Type*) [Field F] := {v : F × F // v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ v.1 ≠ v.2}

def pairFirst (σ : Fˣ) (d t : F) : F := (σ:F)*d*t/(t-1)
def pairSecond (σ : Fˣ) (d t : F) : F := (σ:F)*d/(t-1)

theorem pair_difference (σ : Fˣ) (d t : F) (ht : t ≠ 1) :
    pairFirst σ d t-pairSecond σ d t = (σ:F)*d := by
  dsimp [pairFirst, pairSecond]
  field_simp

theorem pair_ratio (σ : Fˣ) (d t : F) (hd : d ≠ 0) (ht : t ≠ 1) :
    pairFirst σ d t/pairSecond σ d t = t := by
  dsimp [pairFirst, pairSecond]
  field_simp

def pairCoordinates (σ : Fˣ) : PairInput F ≃ PairOutput F where
  toFun v := ⟨(pairFirst σ v.1.1 v.1.2, pairSecond σ v.1.1 v.1.2), by
    have hd := v.property.1
    have ht0 := v.property.2.1
    have ht1 := v.property.2.2
    refine ⟨div_ne_zero (mul_ne_zero (mul_ne_zero (Units.ne_zero σ) hd) ht0)
      (sub_ne_zero.mpr ht1),
      div_ne_zero (mul_ne_zero (Units.ne_zero σ) hd) (sub_ne_zero.mpr ht1), ?_⟩
    intro h
    change pairFirst σ v.1.1 v.1.2 = pairSecond σ v.1.1 v.1.2 at h
    have hh := pair_difference σ v.1.1 v.1.2 ht1
    rw [h, sub_self] at hh
    exact mul_ne_zero (Units.ne_zero σ) hd hh.symm⟩
  invFun v := ⟨((v.1.1-v.1.2)/(σ:F), v.1.1/v.1.2), by
    refine ⟨div_ne_zero (sub_ne_zero.mpr v.property.2.2) (Units.ne_zero σ),
      div_ne_zero v.property.1 v.property.2.1, ?_⟩
    exact fun h => v.property.2.2 ((div_eq_one_iff_eq v.property.2.1).mp h)⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      rw [pair_difference σ v.1.1 v.1.2 v.property.2.2]
      exact mul_div_cancel_left₀ _ (Units.ne_zero σ)
    · exact pair_ratio σ v.1.1 v.1.2 v.property.1 v.property.2.2
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp [pairFirst]
      have hz := v.property.2.1
      have hdiff := sub_ne_zero.mpr v.property.2.2
      field_simp
    · dsimp [pairSecond]
      have hz := v.property.2.1
      have hdiff := sub_ne_zero.mpr v.property.2.2
      field_simp

end
end Ostmann.FiniteField

end OAI
