import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalFourierCharacter
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalDilation

namespace OAI

/-! Fourier observations on the literal half-open cell, under translation
and integral dilation. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaHorizontalFourierCoefficient (h : Eisenstein) (f : ℂ → ℂ) : ℂ :=
  ∫ z in cubicThetaHorizontalCell,star (cubicThetaHorizontalCharacter h z)*f z

lemma cubicThetaHorizontalFourier_integrand_periodic (h : Eisenstein) (f : ℂ → ℂ)
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) (w : Eisenstein) (z : ℂ) :
    star (cubicThetaHorizontalCharacter h (z+3*(w:ℂ)))*f (z+3*(w:ℂ))=
      star (cubicThetaHorizontalCharacter h z)*f z := by
  rw [cubicThetaHorizontalCharacter_periodic,hf]

lemma cubicThetaHorizontalFourier_translate (h : Eisenstein) (f : ℂ → ℂ)
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) (b : ℂ) :
    cubicThetaHorizontalFourierCoefficient h (fun z => f (z+b))=
      cubicThetaHorizontalCharacter h b*cubicThetaHorizontalFourierCoefficient h f := by
  let g := fun z => star (cubicThetaHorizontalCharacter h z)*f z
  have he := cubicThetaHorizontal_translate_integral g
    (cubicThetaHorizontalFourier_integrand_periodic h f hf) b
  have hint : (∫ z in cubicThetaHorizontalCell,g (z+b))=
      star (cubicThetaHorizontalCharacter h b)*
        cubicThetaHorizontalFourierCoefficient h (fun z => f (z+b)) := by
    rw [cubicThetaHorizontalFourierCoefficient,←integral_const_mul]
    apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
    intro z _
    dsimp only [g]
    rw [cubicThetaHorizontalCharacter_add,star_mul]
    ring
  rw [hint] at he
  have hu : cubicThetaHorizontalCharacter h b*star (cubicThetaHorizontalCharacter h b)=1 := by
    rw [mul_comm]
    exact cubicThetaHorizontalCharacter_unit h b
  calc
    _ = (cubicThetaHorizontalCharacter h b*star (cubicThetaHorizontalCharacter h b))*
        cubicThetaHorizontalFourierCoefficient h (fun z => f (z+b)) := by rw [hu,one_mul]
    _ = _ := by rw [mul_assoc,he]; rfl

lemma cubicThetaHorizontalCharacter_mul_index (a h : Eisenstein) (z : ℂ) :
    cubicThetaHorizontalCharacter (a*h) z=cubicThetaHorizontalCharacter h ((a:ℂ)*z) := by
  unfold cubicThetaHorizontalCharacter cubicThetaRowFrequency
  congr 2
  unfold tracePair
  push_cast
  congr 2
  ring

theorem cubicThetaHorizontalFourier_dilate (f : ℂ → ℂ)
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    {a : Eisenstein} (ha : a≠0) (h : Eisenstein)
    (hi : IntegrableOn (fun z => star (cubicThetaHorizontalCharacter h z)*f z) cubicThetaHorizontalCell) :
    cubicThetaHorizontalFourierCoefficient (a*h) (fun z => f ((a:ℂ)*z))=
      cubicThetaHorizontalFourierCoefficient h f := by
  unfold cubicThetaHorizontalFourierCoefficient
  simp_rw [cubicThetaHorizontalCharacter_mul_index]
  exact cubicThetaHorizontal_mul_integral ha (fun z => star (cubicThetaHorizontalCharacter h z)*f z)
    (cubicThetaHorizontalFourier_integrand_periodic h f hf) hi

end CubicFirstMoment

end

end OAI
