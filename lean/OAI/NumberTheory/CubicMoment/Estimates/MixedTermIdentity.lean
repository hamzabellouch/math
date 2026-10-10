import OAI.NumberTheory.CubicMoment.Estimates.TypeIMixedFinite
import OAI.NumberTheory.CubicMoment.Estimates.MixedModelCoprime
import OAI.NumberTheory.CubicMoment.Estimates.DispersionMixedAlgebra

namespace OAI

/-! Connect the literal Type-I sums to the exact mixed term and its
coprimality model; this is purely finite algebra and power normalization. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma typeIMixedModel_eq_mass (r : Eisenstein) (W : ℝ → ℂ) (A : ℝ) :
    typeIMixedModel r W A =
      ((cStar*norm r^(-1/6:ℝ):ℝ):ℂ)*coprimeSquarefreeModelMass r W A := by
  rw [typeIMixedModel,coprimeSquarefreeModelMass,←tsum_mul_left]
  apply tsum_congr
  intro a
  by_cases ha : primary a
  · simp only [ha,ite_true]
    have hn : 0 < norm a := norm_pos_of_ne_zero (primary_ne_zero ha)
    have hp : norm (r*a)^(-1/6:ℝ)*norm a^(-1/6:ℝ) =
        norm r^(-1/6:ℝ)*norm a^(-1/3:ℝ) := by
      rw [norm_mul_eq,Real.mul_rpow (norm_nonneg r) hn.le,mul_assoc,←Real.rpow_add hn]
      norm_num
    calc
      _ = (idealMoebius (r*a):ℂ)^2*
          ((cStar*(norm (r*a)^(-1/6:ℝ)*norm a^(-1/6:ℝ)):ℝ):ℂ)*W (norm a/A) := by push_cast; ring
      _ = _ := by rw [hp]; push_cast; ring
  · simp only [ha,ite_false,mul_zero]

lemma typeIMixedModel_sum_eq (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    (∑ b ∈ S, β b*normTwist u b*typeIMixedModel b W A) = mixedMassModel S β u W A := by
  unfold mixedMassModel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [typeIMixedModel_eq_mass]
  push_cast
  ring

lemma typeIMixedGauss_sum_eq (S : Finset Eisenstein) (hS : ∀ b ∈ S, primary b)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) {A R F : ℝ}
    (hA : 0 < A) (hRF : R*A ≤ F) (hcut : ∀ x, R < x → W x = 0) :
    (∑ b ∈ S, β b*normTwist u b*typeIMixedGauss b W A) =
      ∑ a ∈ primaryElementBall F, (idealMoebius a:ℂ)^2*W (norm a/A)*gauss a*
        ((norm a^(-1/6:ℝ):ℝ):ℂ)*dispersionPolynomial S β u a := by
  calc
    _ = ∑ b ∈ S, β b*normTwist u b*(∑ a ∈ primaryElementBall F,
        (W (norm a/A)*((norm a^(-1/6:ℝ):ℝ):ℂ))*gauss (a*b)) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [typeIMixedGauss_finite b W hA hRF hcut]
    _ = ∑ a ∈ primaryElementBall F, (idealMoebius a:ℂ)^2*
        (W (norm a/A)*((norm a^(-1/6:ℝ):ℝ):ℂ))*gauss a*dispersionPolynomial S β u a :=
      (dispersion_mixed_finite _ _ (fun a ha => (mem_primaryElementBall.mp ha).1)
        hS _ β u).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      ring

end CubicFirstMoment

end

end OAI
