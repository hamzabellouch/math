import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSieveProjection
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryIndex

namespace OAI

/-! The primary projection written as the literal squarefree/cube Gauss
expansion, using the proved unnormalized coefficient formula. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimaryNumerator_ne_zero (cd : CubicThetaPrimaryPair) :
    cubicThetaPrimaryNumerator cd ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero lambdaE_prime.ne_zero (primary_ne_zero cd.property.1))
    (pow_ne_zero _ (primary_ne_zero cd.property.2.1))

lemma cubicThetaPrimary_gauss_term (cd : CubicThetaPrimaryPair) (z : ℂ) (v : ℝ) :
    cubicThetaSeriesTerm cubicThetaConjugateCoefficient z v (cubicThetaPrimaryNumerator cd) =
      ((3^(5/2:ℝ)*Real.sqrt (norm cd.val.2):ℝ):ℂ)*gauss cd.val.1*
        ((v:ℂ)/2)*(cubicBesselKernel ((2*Real.pi*‖cubicThetaFrequency
          (cubicThetaPrimaryNumerator cd)‖*v)^2):ℂ)*
        (Real.fourierChar (tracePair (cubicThetaFrequency (cubicThetaPrimaryNumerator cd)) z):ℂ) := by
  have he := cubicThetaTau_primary_conj cd.property.1 cd.property.2.1 cd.property.2.2
  change star ((‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖:ℂ)*
    cubicThetaArithmeticCoefficient (cubicThetaPrimaryNumerator cd)) = _ at he
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal] at he
  have he' : star (cubicThetaArithmeticCoefficient (cubicThetaPrimaryNumerator cd))*
      (‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖:ℂ) =
      ((3^(5/2:ℝ):ℝ):ℂ)*(Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1 := by
    simpa only [←Complex.star_def,Complex.ofReal_mul] using he
  simp only [cubicThetaSeriesTerm,cubicThetaPrimaryNumerator_ne_zero cd,ite_false,
    cubicThetaConjugateCoefficient,cubicThetaWhittaker,Complex.ofReal_mul]
  have hp : (2*Real.pi*(‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖*v))^2 =
      (2*Real.pi*‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖*v)^2 := by ring
  rw [hp]
  calc
    _ = (star (cubicThetaArithmeticCoefficient (cubicThetaPrimaryNumerator cd))*
        (‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖:ℂ))*
        ((v:ℂ)/2)*(cubicBesselKernel ((2*Real.pi*‖cubicThetaFrequency
          (cubicThetaPrimaryNumerator cd)‖*v)^2):ℂ)*
        (Real.fourierChar (tracePair (cubicThetaFrequency (cubicThetaPrimaryNumerator cd)) z):ℂ) := by ring
    _ = _ := congrArg (fun w : ℂ => w*((v:ℂ)/2)*
      (cubicBesselKernel ((2*Real.pi*‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖*v)^2):ℂ)*
      (Real.fourierChar (tracePair (cubicThetaFrequency (cubicThetaPrimaryNumerator cd)) z):ℂ)) he' 

/-- The exact Gauss series that will be transformed in the Voronoi proof. -/
theorem cubicThetaSelected_gauss_expansion (z : ℂ) (v : ℝ) :
    cubicThetaNonconstant cubicThetaSelectedCoefficient (z,v) =
      ∑' cd : CubicThetaPrimaryPair,
        ((3^(5/2:ℝ)*Real.sqrt (norm cd.val.2):ℝ):ℂ)*gauss cd.val.1*
          ((v:ℂ)/2)*(cubicBesselKernel ((2*Real.pi*‖cubicThetaFrequency
            (cubicThetaPrimaryNumerator cd)‖*v)^2):ℂ)*
          (Real.fourierChar (tracePair (cubicThetaFrequency (cubicThetaPrimaryNumerator cd)) z):ℂ) := by
  unfold cubicThetaNonconstant
  calc
    _ = ∑' n : Eisenstein, if cubicThetaPrimarySupport n then
        cubicThetaSeriesTerm cubicThetaConjugateCoefficient z v n else 0 := by
      apply tsum_congr
      intro n
      by_cases hn : cubicThetaPrimarySupport n
      · simp only [hn,ite_true,cubicThetaSeriesTerm,cubicThetaSelectedCoefficient]
      · simp [hn,cubicThetaSeriesTerm,cubicThetaSelectedCoefficient]
    _ = ∑' cd : CubicThetaPrimaryPair,
        cubicThetaSeriesTerm cubicThetaConjugateCoefficient z v (cubicThetaPrimaryNumerator cd) :=
      cubicThetaPrimary_tsum _
    _ = _ := tsum_congr (fun cd => cubicThetaPrimary_gauss_term cd z v)

end CubicFirstMoment

end

end OAI
