import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalFourierTranslation

namespace OAI

/-! Orthogonality of the literal trace characters on the half-open
three-Eisenstein cell, including its unnormalized volume. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalCharacter_add_index (h k : Eisenstein) (z : ℂ) :
    cubicThetaHorizontalCharacter (h+k) z=
      cubicThetaHorizontalCharacter h z*cubicThetaHorizontalCharacter k z := by
  unfold cubicThetaHorizontalCharacter cubicThetaRowFrequency
  have he : tracePair z ((↑(h+k):ℂ)/(3*traceLambda))=
      tracePair z ((h:ℂ)/(3*traceLambda))+tracePair z ((k:ℂ)/(3*traceLambda)) := by
    unfold tracePair
    push_cast
    rw [add_div,mul_add,Complex.add_re]
    ring
  rw [he,AddChar.map_add_eq_mul,Circle.coe_mul]

lemma cubicThetaHorizontalCharacter_inner (h k : Eisenstein) (z : ℂ) :
    star (cubicThetaHorizontalCharacter h z)*cubicThetaHorizontalCharacter k z=
      cubicThetaHorizontalCharacter (k-h) z := by
  have he := cubicThetaHorizontalCharacter_add_index h (k-h) z
  rw [add_sub_cancel] at he
  rw [he,←mul_assoc,cubicThetaHorizontalCharacter_unit,one_mul]

lemma cubicThetaHorizontalCharacter_nontrivial {h : Eisenstein} (hh : h≠0) :
    ∃ b : ℂ,cubicThetaHorizontalCharacter h b≠1 := by
  obtain ⟨t,ht⟩ := AddChar.ne_one_iff.mp Real.fourierChar_ne_one
  have hw : cubicThetaRowFrequency h≠0 := by
    unfold cubicThetaRowFrequency
    exact div_ne_zero (fun he => hh (Subtype.ext he)) (mul_ne_zero (by norm_num) traceLambda_ne_zero)
  refine ⟨(t:ℂ)/(2*cubicThetaRowFrequency h),?_⟩
  have he : tracePair ((t:ℂ)/(2*cubicThetaRowFrequency h)) (cubicThetaRowFrequency h)=t := by
    unfold tracePair
    have he' : (t:ℂ)/(2*cubicThetaRowFrequency h)*cubicThetaRowFrequency h=(t:ℂ)/2 := by
      field_simp
    rw [he']
    simp
    ring
  unfold cubicThetaHorizontalCharacter
  rw [he]
  intro hz
  exact ht (Subtype.ext hz)

theorem cubicThetaHorizontalFourier_character_zero {h k : Eisenstein} (hhk : h≠k) :
    cubicThetaHorizontalFourierCoefficient h (cubicThetaHorizontalCharacter k)=0 := by
  let d := k-h
  have hd : d≠0 := sub_ne_zero.mpr (Ne.symm hhk)
  obtain ⟨b,hb⟩ := cubicThetaHorizontalCharacter_nontrivial hd
  let I := ∫ z in cubicThetaHorizontalCell,cubicThetaHorizontalCharacter d z
  have he := cubicThetaHorizontal_translate_integral (cubicThetaHorizontalCharacter d)
    (fun w z => cubicThetaHorizontalCharacter_periodic d w z) b
  have he' : cubicThetaHorizontalCharacter d b*I=I := by
    rw [show (fun z => cubicThetaHorizontalCharacter d (z+b))=
      (fun z => cubicThetaHorizontalCharacter d b*cubicThetaHorizontalCharacter d z) from
      funext (fun z => by rw [cubicThetaHorizontalCharacter_add,mul_comm]),integral_const_mul] at he
    exact he
  have hI : I=0 := by
    by_contra hn
    apply hb
    apply mul_right_cancel₀ hn
    simpa only [one_mul] using he'
  unfold cubicThetaHorizontalFourierCoefficient
  simp_rw [cubicThetaHorizontalCharacter_inner]
  exact hI

end CubicFirstMoment

end

end OAI
