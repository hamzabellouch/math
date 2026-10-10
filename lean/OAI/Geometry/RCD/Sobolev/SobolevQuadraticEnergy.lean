import OAI.Geometry.RCD.Sobolev.LocalBochnerInput

namespace OAI

/-! # Exact source energy expansion for harmonic test perturbations -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem localGamma_add_smul_square (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (f g : SobolevSpace μ hQ) (t : ℝ) :
    localGamma μ hQ (f+t • g) (f+t • g)=ᵐ[μ]
      fun x => localGamma μ hQ f f x+2*t*localGamma μ hQ f g x+
        t^2*localGamma μ hQ g g x := by
  filter_upwards [localGamma_add_left μ hQ f (t • g) (f+t • g),
    localGamma_add_right μ hQ f f (t • g),
    localGamma_add_right μ hQ (t • g) f (t • g),
    localGamma_smul_right μ hQ t f g,localGamma_smul_left μ hQ t g f,
    localGamma_smul_left μ hQ t g (t • g),localGamma_smul_right μ hQ t g g,
    localGamma_comm μ hQ g f] with x ha hb hc hd he hf hg hh
  rw [ha,hb,hc,hd,he,hf,hg,hh]
  ring

theorem integral_localGamma_add_smul_square (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (f g : SobolevSpace μ hQ) (t : ℝ) (A : Set X) :
    (∫ x in A, localGamma μ hQ (f+t • g) (f+t • g) x ∂μ)=
      (∫ x in A, localGamma μ hQ f f x ∂μ)+
        2*t*(∫ x in A, localGamma μ hQ f g x ∂μ)+
        t^2*(∫ x in A, localGamma μ hQ g g x ∂μ) := by
  rw [integral_congr_ae (ae_restrict_of_ae (localGamma_add_smul_square μ hQ f g t))]
  have hff : Integrable (localGamma μ hQ f f) (μ.restrict A) := (localGamma_memL1 μ hQ f f).restrict
  have hfg : Integrable (localGamma μ hQ f g) (μ.restrict A) := (localGamma_memL1 μ hQ f g).restrict
  have hgg : Integrable (localGamma μ hQ g g) (μ.restrict A) := (localGamma_memL1 μ hQ g g).restrict
  have hsum := integral_add (hff.add (hfg.const_mul (2*t))) (hgg.const_mul (t^2))
  have hfirst := integral_add hff (hfg.const_mul (2*t))
  simp only [Pi.add_apply] at hsum hfirst
  rw [hsum,hfirst,integral_const_mul,integral_const_mul]

theorem integral_harmonic_perturbation (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (f g : SobolevSpace μ hQ) (t : ℝ) (A : Set X)
    (hg : (∫ x in A, localGamma μ hQ f g x ∂μ)=0) :
    (∫ x in A, localGamma μ hQ (f+t • g) (f+t • g) x ∂μ)=
      (∫ x in A, localGamma μ hQ f f x ∂μ)+
        t^2*(∫ x in A, localGamma μ hQ g g x ∂μ) := by
  rw [integral_localGamma_add_smul_square, hg,mul_zero,add_zero]

end RegularPointCoordinates

end

end OAI
