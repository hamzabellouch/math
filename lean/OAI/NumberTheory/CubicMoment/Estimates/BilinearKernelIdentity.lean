import OAI.NumberTheory.CubicMoment.Estimates.CorrectedBilinearScale
import OAI.NumberTheory.CubicMoment.Angular.AngularLatticeModel

namespace OAI

/-! The factored correction and the original squarefree product kernel
are related by the explicit shared-prime contribution. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def centeredGauss (a : Eisenstein) : ℂ :=
  gauss a-(cStar:ℂ)*(idealMoebius a:ℂ)^2*((norm a^(-1/6:ℝ):ℝ):ℂ)

def modelOverlap (P B : Finset Eisenstein) (α β : Eisenstein → ℂ) (u : ℝ) : ℂ :=
  ∑ a ∈ P, ∑ b ∈ B, if IsCoprime a b then 0 else
    (cStar:ℂ)*α a*β b*normTwist u a*normTwist u b*(idealMoebius a:ℂ)^2*
      ((norm a^(-1/6:ℝ):ℝ):ℂ)*((norm b^(-1/6:ℝ):ℝ):ℂ)

lemma centered_bilinear_eq_correction_add_overlap (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) (hP : ∀ a ∈ P, primary a)
    (hB : ∀ b ∈ B, primary b ∧ Squarefree b) :
    (∑ a ∈ P, ∑ b ∈ B, α a*β b*centeredGauss (a*b)*normTwist u (a*b)) =
      correctedBilinearSum P B α β u + modelOverlap P B α β u := by
  unfold correctedBilinearSum modelOverlap dispersionModel
  have hm : ((cStar:ℂ)*(∑ b ∈ B, β b*normTwist u b*((norm b^(-1/6:ℝ):ℝ):ℂ)))*
      (∑ a ∈ P, α a*normTwist u a*(if Squarefree a then (1:ℂ) else 0)*
        ((norm a^(-1/6:ℝ):ℝ):ℂ)) =
      ∑ a ∈ P, ∑ b ∈ B, ((cStar:ℂ)*(β b*normTwist u b*((norm b^(-1/6:ℝ):ℝ):ℂ)))*
        (α a*normTwist u a*(if Squarefree a then (1:ℂ) else 0)*((norm a^(-1/6:ℝ):ℝ):ℂ)) := by
    simp only [Finset.mul_sum,Finset.sum_mul]
  rw [hm]
  simp only [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hna := norm_pos_of_ne_zero (primary_ne_zero (hP a ha))
  have hnb := norm_pos_of_ne_zero (primary_ne_zero (hB b hb).1)
  rw [centeredGauss,normTwist_mul u (primary_ne_zero (hP a ha))
    (primary_ne_zero (hB b hb).1),norm_mul_eq,Real.mul_rpow hna.le hnb.le]
  have hμ : (idealMoebius (a*b):ℂ)^2 =
      if IsCoprime a b then (idealMoebius a:ℂ)^2 else 0 := by
    simpa only [mul_comm b a,isCoprime_comm] using
      idealMoebius_sq_mul_of_squarefree (hB b hb).2 a
  rw [hμ,←idealMoebius_sq_complex]
  push_cast
  split_ifs <;> ring

end CubicFirstMoment

end

end OAI
