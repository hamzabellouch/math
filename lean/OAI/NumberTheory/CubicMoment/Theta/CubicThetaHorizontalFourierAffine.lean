import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalFourierAlgebra
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalFourierVanishing

namespace OAI

/-! Divisibility and phase in the Fourier coefficient of an affine slice. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaHorizontalFourier_affine (f : C(ℂ,ℂ))
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    {a : Eisenstein} (ha : a≠0) (h : Eisenstein) (b : ℂ) :
    cubicThetaHorizontalFourierCoefficient (a*h) (fun z => f ((a:ℂ)*z+b))=
      cubicThetaHorizontalCharacter h b*cubicThetaHorizontalFourierCoefficient h f := by
  have hg : ∀ (w : Eisenstein) z,f ((z+3*(w:ℂ))+b)=f (z+b) := by
    intro w z
    rw [add_right_comm z, hf]
  rw [cubicThetaHorizontalFourier_dilate (fun z => f (z+b)) hg ha h
    (cubicThetaHorizontalFourier_integrable h _
      (f.continuous.comp (continuous_id.add continuous_const)))]
  exact cubicThetaHorizontalFourier_translate h f hf b

theorem cubicThetaHorizontalFourier_affine_zero (f : ℂ → ℂ)
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    {a : Eisenstein} (ha : a≠0) (h : Eisenstein) (hh : ¬a∣h) (b : ℂ) :
    cubicThetaHorizontalFourierCoefficient h (fun z => f ((a:ℂ)*z+b))=0 := by
  apply cubicThetaHorizontalFourier_dilate_zero (fun z => f (z+b)) _ ha h hh
  intro w z
  rw [add_right_comm z,hf]

end CubicFirstMoment

end

end OAI
