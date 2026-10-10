import OAI.NumberTheory.CubicMoment.Estimates.CorrectedSquareExpansion
import OAI.NumberTheory.CubicMoment.Estimates.FiniteDispersionWeights

namespace OAI

/-! The genuine squarefree corrected variance, with its exact finite
support reduction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def correctedSquareMass (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℝ) (A : ℝ) : ℝ :=
  ∑' a : Eisenstein, if primary a then (idealMoebius a:ℝ)^2*V (norm a/A)*
    ‖correctedDispersionPolynomial S β u a‖^2 else 0

lemma correctedSquareMass_eq_sum (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℝ) {A R F : ℝ} (hA : 0 < A) (hRF : R*A ≤ F)
    (hcut : ∀ x, R < x → V x = 0) :
    correctedSquareMass S β u V A = ∑ a ∈ primaryElementBall F,
      (idealMoebius a:ℝ)^2*V (norm a/A)*‖correctedDispersionPolynomial S β u a‖^2 := by
  unfold correctedSquareMass
  calc
    _ = ∑ a ∈ primaryElementBall F, if primary a then
        (idealMoebius a:ℝ)^2*V (norm a/A)*‖correctedDispersionPolynomial S β u a‖^2 else 0 := by
      apply tsum_eq_sum
      intro a ha
      by_cases hp : primary a
      · have hn : R < norm a/A := (lt_div_iff₀ hA).mpr
          (hRF.trans_lt (lt_of_not_ge (fun hn => ha (mem_primaryElementBall.mpr ⟨hp,hn⟩))))
        simp only [hcut _ hn,mul_zero,zero_mul,ite_self]
      · simp only [hp,ite_false]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [ite_eq_left (mem_primaryElementBall.mp ha).1]

lemma correctedSquareMass_nonneg (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x) (A : ℝ) :
    0 ≤ correctedSquareMass S β u V A := by
  apply tsum_nonneg
  intro a
  split_ifs
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (hV _)) (sq_nonneg _)
  · exact le_rfl

end CubicFirstMoment

end

end OAI
