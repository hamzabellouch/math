import OAI.NumberTheory.CubicMoment.Angular.AngularKummerAlgebra
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedBeta
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedMoment

namespace OAI

/-! Selected-side prime cancellation applies to the literal
stoppedBeta coefficient, with its global-largest role selected exactly. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_stoppedBeta_selected_identity (ℓ : ℤ) {B ρ a b w u : ℝ} {j j₀ k h : ℕ}
    (hj : j < geometricBinCount ρ B) (Z Q : ℝ) (early : Bool)
    (R : Finset Eisenstein) (hR : ∀ r ∈ R, primary r)
    (f : Eisenstein → ℂ) (v e : Eisenstein) :
    (∑ n ∈ primaryPairSupport R (primaryElementBall B),
      stoppedBeta R (primaryElementBall B) f primeDetectorCutoff w
        (stoppedSelectedTest B ρ j j₀ k h Z Q early) n *
      (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
        then normTwist u n*angularCubicSymbol ℓ n v else 0)) =
      ∑ r ∈ R, f r*∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
        cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*angularCubicSymbol ℓ (r*d) v := by
  unfold stoppedBeta
  rw [primaryPairCoefficient_sum,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r hr
  rw [selectedStoppedDivisorSet_eq hj Z Q early r e (hR r hr),Finset.mul_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases ht : stoppedSelectedTest B ρ j j₀ k h Z Q early r d
  · by_cases hc : Squarefree (r*d) ∧ IsCoprime (r*d) e ∧ a < norm (r*d) ∧ norm (r*d) ≤ b
    · simp only [ht,hc,and_self,ite_true]
      ring
    · simp only [ht,hc,false_and,ite_false,mul_zero]
  · simp only [ht,and_false,ite_false,zero_mul]

end CubicFirstMoment

end

end OAI
