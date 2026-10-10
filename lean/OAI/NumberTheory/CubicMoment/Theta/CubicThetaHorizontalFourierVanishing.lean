import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalFourierTranslation
import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveResidueFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalAffine

namespace OAI

/-! Dilation kills precisely the horizontal frequencies outside the
corresponding principal ideal, by the primitive finite trace pairing. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaHorizontalCharacter_fraction (h q b : Eisenstein) (hq : q≠0) :
    cubicThetaHorizontalCharacter h (3*(b:ℂ)/(q:ℂ))=
      residueFourierChar q hq (Ideal.Quotient.mk (modulus q) (h*b)) := by
  rw [residueFourierChar_mk]
  unfold cubicThetaHorizontalCharacter
  congr 2
  unfold tracePair cubicThetaRowFrequency
  push_cast
  congr 2
  field_simp [traceLambda_ne_zero]

theorem cubicThetaHorizontalFourier_dilate_zero (f : ℂ → ℂ)
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    {a : Eisenstein} (ha : a≠0) (h : Eisenstein) (hh : ¬a∣h) :
    cubicThetaHorizontalFourierCoefficient h (fun z => f ((a:ℂ)*z))=0 := by
  have hn : Ideal.Quotient.mk (modulus a) h≠0 := by
    intro hz
    exact hh (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  obtain ⟨b,hb⟩ := AddChar.ne_one_iff.mp (residueFourierChar_isPrimitive a ha hn)
  let m := residueRepresentative a b
  have hm : Ideal.Quotient.mk (modulus a) m=b := residueRepresentative_spec a b
  let F : ℂ → ℂ := fun z => f ((a:ℂ)*z)
  have hF : ∀ (w : Eisenstein) z,F (z+3*(w:ℂ))=F z :=
    cubicThetaHorizontal_multiply_periodic f hf a
  have htrans : (fun z => F (z+3*(m:ℂ)/(a:ℂ)))=F := by
    funext z
    change f ((a:ℂ)*(z+3*(m:ℂ)/(a:ℂ)))=f ((a:ℂ)*z)
    have he : (a:ℂ)*(z+3*(m:ℂ)/(a:ℂ))=(a:ℂ)*z+3*(m:ℂ) := by
      have haC : (a:ℂ)≠0 := fun hz => ha (Subtype.ext hz)
      field_simp
    rw [he,hf]
  have he := cubicThetaHorizontalFourier_translate h F hF (3*(m:ℂ)/(a:ℂ))
  rw [htrans] at he
  have hc : cubicThetaHorizontalCharacter h (3*(m:ℂ)/(a:ℂ))≠1 := by
    rw [cubicThetaHorizontalCharacter_fraction h a m ha,map_mul,hm]
    exact hb
  by_contra hz
  apply hc
  apply mul_right_cancel₀ hz
  simpa only [one_mul] using he.symm

end CubicFirstMoment

end

end OAI
