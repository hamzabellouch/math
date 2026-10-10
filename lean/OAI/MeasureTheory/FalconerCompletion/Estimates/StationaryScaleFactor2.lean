import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.StationaryScaleFactor
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAmbient2

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell

lemma stationary_scale_factorND (M K : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) (A : ℝ) :
    Λ^(-(M:ℝ))*A^(2*M+K) = (A^2/Λ)^M*A^K := by
  rw [Real.rpow_neg hΛ.le,Real.rpow_natCast,pow_add,div_pow,pow_mul]
  ring

theorem stationary_scale_decayND (M K : ℕ) {R A Λ κ : ℝ}
    (hR : 1 ≤ R) (hA : 1 ≤ A) (hΛ : 0 < Λ)
    (hupper : A ≤ R^2) (hratio : A^2/Λ ≤ R^(-κ)) :
    Λ^(-(M:ℝ))*A^(2*M+K) ≤ R^(-κ*(M:ℝ)+2*(K:ℝ)) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  rw [stationary_scale_factorND M K hΛ]
  calc
    _ ≤ (R^(-κ))^M * (R^2)^K := by
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hratio M)
        (pow_le_pow_left₀ (by linarith) hupper K) (by positivity) (by positivity)
    _ = _ := by
      rw [← pow_mul,← Real.rpow_natCast (R^(-κ)) M,← Real.rpow_mul hRp.le,
        ← Real.rpow_natCast R (2*K),← Real.rpow_add hRp]
      congr 1
      push_cast
      ring

lemma exists_stationary_orderND (κ T : ℝ) (hκ : 0 < κ) (K : ℕ) :
    ∃ J : ℕ, -κ*((J+1:ℕ):ℝ)+2*(K:ℝ) ≤ -T := by
  obtain ⟨J,hJ⟩ := exists_nat_gt ((T+2*(K:ℝ))/κ)
  refine ⟨J,?_⟩
  have h₁ := (div_lt_iff₀ hκ).mp hJ
  push_cast
  nlinarith

theorem stationary_arbitrary_powerND (κ T : ℝ) (hκ : 0 < κ) (K : ℕ) :
    ∃ J : ℕ, ∀ R A Λ : ℝ, 1 ≤ R → 1 ≤ A → 0 < Λ →
      A ≤ R^2 → A^2/Λ ≤ R^(-κ) →
      Λ^(-((J+1:ℕ):ℝ))*A^(2*(J+1)+K) ≤ R^(-T) := by
  obtain ⟨J,hJ⟩ := exists_stationary_orderND κ T hκ K
  refine ⟨J,?_⟩
  intro R A Λ hR hA hΛ hup hratio
  exact (stationary_scale_decayND (J+1) K hR hA hΛ hup hratio).trans
    (Real.rpow_le_rpow_of_exponent_le hR hJ)

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
