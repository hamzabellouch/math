import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalFourierIntegrability

namespace OAI

/-! Linearity of the literal horizontal Fourier observation. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalFourier_integrable_of_integrable (h : Eisenstein)
    {f : ℂ → ℂ} (hf : IntegrableOn f cubicThetaHorizontalCell) :
    IntegrableOn (fun z => star (cubicThetaHorizontalCharacter h z)*f z)
      cubicThetaHorizontalCell := by
  apply hf.bdd_mul (cubicThetaHorizontalCharacter_continuous h).star.aestronglyMeasurable
    (c:=1)
  filter_upwards with z
  simp [cubicThetaHorizontalCharacter]

lemma cubicThetaHorizontalFourier_add (h : Eisenstein) (f g : ℂ → ℂ)
    (hf : IntegrableOn f cubicThetaHorizontalCell)
    (hg : IntegrableOn g cubicThetaHorizontalCell) :
    cubicThetaHorizontalFourierCoefficient h (f+g)=
      cubicThetaHorizontalFourierCoefficient h f+cubicThetaHorizontalFourierCoefficient h g := by
  unfold cubicThetaHorizontalFourierCoefficient
  simp only [Pi.add_apply,mul_add]
  exact integral_add (cubicThetaHorizontalFourier_integrable_of_integrable h hf)
    (cubicThetaHorizontalFourier_integrable_of_integrable h hg)

lemma cubicThetaHorizontalFourier_const_mul (h : Eisenstein) (c : ℂ) (f : ℂ → ℂ) :
    cubicThetaHorizontalFourierCoefficient h (fun z => c*f z)=
      c*cubicThetaHorizontalFourierCoefficient h f := by
  unfold cubicThetaHorizontalFourierCoefficient
  rw [←integral_const_mul]
  congr 1
  funext z
  ring

lemma cubicThetaHorizontalFourier_sum {ι : Type*} (s : Finset ι)
    (h : Eisenstein) (f : ι → ℂ → ℂ) (hf : ∀ i ∈ s,Continuous (f i)) :
    cubicThetaHorizontalFourierCoefficient h (fun z => ∑ i ∈ s,f i z)=
      ∑ i ∈ s,cubicThetaHorizontalFourierCoefficient h (f i) := by
  unfold cubicThetaHorizontalFourierCoefficient
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum s (fun i hi => cubicThetaHorizontalFourier_integrable h _ (hf i hi))

end CubicFirstMoment

end

end OAI
