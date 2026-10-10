import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSelectedTransform
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGaussMellin

namespace OAI

/-! Exact primary-pair reindexing of the smoothed additive sum. The common
numerator is lambda*c*d^3, so the squared frequency is N(c)N(d)^3/27. -/
noncomputable section
open Set
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaSelectedSmoothSum (ℓ : ℤ) (z : ℂ) (W : ℝ→ℂ) (Z : ℝ) : ℂ :=
  ∑' n : MetaplecticDualArgument,theta ℓ n.val*
    cubicThetaCoefficientTwist cubicThetaSelectedCoefficient z n.val*
      (‖cubicThetaFrequency n.val‖:ℂ)*W (‖cubicThetaFrequency n.val‖^2/Z)

lemma cubicThetaSelectedAdditiveSum_eq (g : SL(2,Eisenstein)) (rev : Bool)
    (k : ℕ) (W : ℝ→ℂ) (Z : ℝ) :
    cubicThetaSelectedAdditiveSum g rev k W Z=
      cubicThetaSelectedSmoothSum (cubicThetaCircleOrder (!rev) k)
        (cubicThetaPrimaryCuspCenter g) W Z := rfl

lemma cubicThetaPrimary_smooth_term (cd : CubicThetaPrimaryPair) (ℓ : ℤ)
    (z : ℂ) (W : ℝ→ℂ) (Z : ℝ) :
    theta ℓ (cubicThetaPrimaryNumerator cd)*
      cubicThetaCoefficientTwist cubicThetaConjugateCoefficient z (cubicThetaPrimaryNumerator cd)*
      (‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖:ℂ)*
      W (‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖^2/Z)=
    ((3^(5/2:ℝ):ℝ):ℂ)*theta ℓ lambdaE*
      ((Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*theta ℓ (cd.val.1*cd.val.2^3)*
        (Real.fourierChar (tracePair (cubicThetaFrequency (cubicThetaPrimaryNumerator cd)) z):ℂ)*
        W (norm cd.val.1*norm cd.val.2^3/(27*Z))) := by
  have he := cubicThetaTau_primary_conj cd.property.1 cd.property.2.1 cd.property.2.2
  change star ((‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖:ℂ)*
    cubicThetaArithmeticCoefficient (cubicThetaPrimaryNumerator cd))=_ at he
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal] at he
  have he' : cubicThetaConjugateCoefficient (cubicThetaPrimaryNumerator cd)*
      (‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖:ℂ)=
      ((3^(5/2:ℝ):ℝ):ℂ)*(Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1 := by
    simpa only [cubicThetaConjugateCoefficient,←Complex.star_def,Complex.ofReal_mul] using he
  rw [cubicThetaPrimaryFrequency_sq,div_div]
  have ht : theta ℓ (cubicThetaPrimaryNumerator cd)=
      theta ℓ lambdaE*theta ℓ (cd.val.1*cd.val.2^3) := by
    simp only [cubicThetaPrimaryNumerator,theta_mul,mul_assoc]
  rw [ht,cubicThetaCoefficientTwist]
  calc
    _ = (cubicThetaConjugateCoefficient (cubicThetaPrimaryNumerator cd)*
        (‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖:ℂ))*
      (theta ℓ lambdaE*theta ℓ (cd.val.1*cd.val.2^3)*
        (Real.fourierChar (tracePair (cubicThetaFrequency (cubicThetaPrimaryNumerator cd)) z):ℂ)*
        W (norm cd.val.1*norm cd.val.2^3/(27*Z))) := by ring
    _ = _ := by rw [he']; ring

/-- This reindexing is an identity of the actual sum, with no convergence
hypothesis hidden in a change of variables. -/
theorem cubicThetaSelectedSmoothSum_pairs (ℓ : ℤ) (z : ℂ) (W : ℝ→ℂ) (Z : ℝ) :
    cubicThetaSelectedSmoothSum ℓ z W Z=
    ((3^(5/2:ℝ):ℝ):ℂ)*theta ℓ lambdaE*
      ∑' cd : CubicThetaPrimaryPair,
        (Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*theta ℓ (cd.val.1*cd.val.2^3)*
          (Real.fourierChar (tracePair (cubicThetaFrequency (cubicThetaPrimaryNumerator cd)) z):ℂ)*
          W (norm cd.val.1*norm cd.val.2^3/(27*Z)) := by
  let f (n : Eisenstein) : ℂ := theta ℓ n*
    cubicThetaCoefficientTwist cubicThetaSelectedCoefficient z n*
      (‖cubicThetaFrequency n‖:ℂ)*W (‖cubicThetaFrequency n‖^2/Z)
  have hs : Function.support f ⊆ {n | n≠0} := by
    intro n hn hz
    subst n
    exact hn (by simp [f,cubicThetaFrequency])
  change (∑' n : MetaplecticDualArgument,f n.val)=_
  calc
    _ = ∑' n : Eisenstein,f n := tsum_subtype_eq_of_support_subset hs
    _ = ∑' n : Eisenstein,if cubicThetaPrimarySupport n then
        theta ℓ n*cubicThetaCoefficientTwist cubicThetaConjugateCoefficient z n*
          (‖cubicThetaFrequency n‖:ℂ)*W (‖cubicThetaFrequency n‖^2/Z) else 0 := by
      apply tsum_congr
      intro n
      by_cases hn : cubicThetaPrimarySupport n <;>
        simp [f,cubicThetaCoefficientTwist,cubicThetaSelectedCoefficient,hn]
    _ = ∑' cd : CubicThetaPrimaryPair,
        theta ℓ (cubicThetaPrimaryNumerator cd)*
          cubicThetaCoefficientTwist cubicThetaConjugateCoefficient z (cubicThetaPrimaryNumerator cd)*
          (‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖:ℂ)*
          W (‖cubicThetaFrequency (cubicThetaPrimaryNumerator cd)‖^2/Z) := cubicThetaPrimary_tsum _
    _ = _ := by simp_rw [cubicThetaPrimary_smooth_term]; rw [tsum_mul_left]

/-- Scaling the additive cusp by lambda cubed removes the inverse different
from every selected frequency. -/
lemma cubicThetaPrimary_additive_phase (cd : CubicThetaPrimaryPair) (r u : Eisenstein) :
    (Real.fourierChar (tracePair (cubicThetaFrequency (cubicThetaPrimaryNumerator cd))
      ((traceLambda^3*(u:ℂ))/(r:ℂ))):ℂ)=
      additivePhase r (cd.val.1*cd.val.2^3*u) := by
  rw [additivePhase_fourierChar]
  congr 1
  unfold tracePair cubicThetaFrequency cubicThetaPrimaryNumerator
  push_cast
  rw [lambdaE_coe]
  congr 2
  field_simp [traceLambda_ne_zero]

end CubicFirstMoment

end

end OAI
