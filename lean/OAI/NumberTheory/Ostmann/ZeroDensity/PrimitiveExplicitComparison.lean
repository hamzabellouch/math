import Mathlib.Tactic.GCongr
import OAI.NumberTheory.Ostmann.ZeroDensity.PrimitiveErrorBound

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.ZeroDensity

def contourRemainder (B : ℕ) (Q X T : ℝ) : ℝ :=
  Real.sqrt X*(Q*(T+2))^B+
    X*(Q*(T+2))^B/T^(B+1)*(1+Real.log X)^B

theorem contourRemainder_nonneg (B : ℕ) {Q X T : ℝ}
    (hQ : 0 ≤ Q) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    0 ≤ contourRemainder B Q X T := by
  have hl := Real.log_nonneg hX
  unfold contourRemainder
  positivity

theorem contourRemainder_mono (B : ℕ) {q Q X T : ℝ}
    (hq : 0 ≤ q) (hqQ : q ≤ Q) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    contourRemainder B q X T ≤ contourRemainder B Q X T := by
  have hl := Real.log_nonneg hX
  unfold contourRemainder
  gcongr

theorem zero_decay_weight_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset ℂ) (A : ℕ) {X : ℝ} (hX : 0 ≤ X) :
    (∑ p ∈ S, (Ostmann.Dirichlet.zeroMultiplicity χ p : ℝ)*X^p.re/(1+|p.im|)^A) ≤
      ∑ p ∈ S, (Ostmann.Dirichlet.zeroMultiplicity χ p : ℝ)*X^p.re := by
  apply Finset.sum_le_sum
  intro p hp
  apply div_le_self (by positivity)
  exact one_le_pow₀ (by linarith [abs_nonneg p.im] : (1 : ℝ) ≤ 1+|p.im|)

theorem totalPrimitiveError_le_of_truncated_formula (Q : ℕ) (hQ : 0 < Q)
    (φ : ℝ → ℝ) {X T C : ℝ} (B : ℕ) (hX : 1 ≤ X) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hcharacters : ∀ χ : NonprincipalPrimitiveFamily Q,
      ‖smoothError χ.val.2.val φ X‖ ≤ C*
        ((∑ p ∈ (Ostmann.Dirichlet.zerosUpTo_finite χ.1.2.1 χ.2 (T+1)).toFinset.filter
          (fun p => (1 : ℝ)/2 ≤ p.re),
          (Ostmann.Dirichlet.zeroMultiplicity χ.1.2.1 p : ℝ)*X^p.re/(1+|p.im|)^(B+1))+
          contourRemainder B (χ.val.1.val+1 : ℝ) X T)) :
    totalPrimitiveError Q none φ X ≤
      ‖smoothError (1 : DirichletCharacter ℂ 1) φ X‖+
        C*((∑ z ∈ retainedZeros Q none (1/2) (T+1), X^z.point.re)+
          (Q : ℝ)^2*contourRemainder B Q X T) := by
  apply totalPrimitiveError_le_of_explicit_bounds Q hQ φ X (T+1) hC
    (contourRemainder_nonneg B (Nat.cast_nonneg Q) hX hT) (le_refl _)
  intro χ
  refine (hcharacters χ).trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hC)
  · exact zero_decay_weight_le χ.val.2.val _ (B+1) (by linarith)
  · apply contourRemainder_mono B (by positivity) _ hX hT
    exact_mod_cast (show χ.val.1.val+1 ≤ Q from χ.val.1.isLt)

end Ostmann.ZeroDensity

end

end OAI
