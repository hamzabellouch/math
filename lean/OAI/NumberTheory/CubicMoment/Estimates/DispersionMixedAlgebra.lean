import OAI.NumberTheory.CubicMoment.Estimates.DispersionAlgebra
import OAI.NumberTheory.CubicMoment.Angular.AngularLatticeModel

namespace OAI

/-! The mixed term in the corrected square is the genuine Type-I sum.
No coprimality restriction is silently removed. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma moebius_sq_mul_gauss {a : Eisenstein} (ha : primary a) :
    (idealMoebius a:ℂ)^2*gauss a = gauss a := by
  rw [idealMoebius_sq_complex]
  by_cases hs : Squarefree a
  · simp only [hs,ite_true,one_mul]
  · simp only [hs,ite_false,zero_mul,gauss_eq_zero_of_not_squarefree ha hs]

lemma dispersion_mixed_finite (A B : Finset Eisenstein)
    (hA : ∀ a ∈ A, primary a) (hB : ∀ b ∈ B, primary b)
    (W β : Eisenstein → ℂ) (u : ℝ) :
    (∑ a ∈ A, (idealMoebius a:ℂ)^2*W a*gauss a*dispersionPolynomial B β u a) =
      ∑ b ∈ B, β b*normTwist u b*(∑ a ∈ A, W a*gauss (a*b)) := by
  simp_rw [dispersionPolynomial,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  rw [gauss_mul (hA a ha) (hB b hb)]
  have hm := moebius_sq_mul_gauss (hA a ha)
  calc
    _ = W a*(β b*normTwist u b)*((idealMoebius a:ℂ)^2*gauss a)*
        gauss b*star (cubicSymbol b a) := by ring
    _ = _ := by rw [hm]; ring

end CubicFirstMoment

end

end OAI
