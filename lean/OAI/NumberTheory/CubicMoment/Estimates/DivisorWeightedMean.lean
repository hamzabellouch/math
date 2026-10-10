import OAI.NumberTheory.CubicMoment.Estimates.WeightedDivisorEnergy
import OAI.NumberTheory.CubicMoment.Estimates.DivisorCharacterMass

namespace OAI

/-! Ordinary mean values summed over the literal coprimality divisors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisor_weighted_character_height {C T : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hT : 0 < T)
    (S H U : Finset Eisenstein) (β : Eisenstein → ℂ) (Z : ℕ)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) (u : ℝ) :
    dyadicHeightMean (fun t => divisorCharacterMass S H U β (t+u)) T ≤
      2*C*(1+(Z:ℝ)/T)*(∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2)*H.card := by
  let F := fun s : Finset Eisenstein => S.filter (fun b => (∏ p ∈ s, p) ∣ b)
  let E := fun s => ∑ b ∈ F s, (4:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2
  have hrow (s : Finset Eisenstein) :
      dyadicHeightMean (fun t => finiteCharacterMass (F s) H β (t+u)) T ≤
        2*C*(1+(Z:ℝ)/T)*E s*H.card := by
    simpa only [finiteCharacterMass,theta_zero,mul_one] using
      squarefree_weighted_character_height hMV hC hT (F s) H β Z
        (fun b hb => hS b (Finset.mem_filter.mp hb).1) u 0
  unfold divisorCharacterMass
  rw [dyadicHeightMean_sum U.powerset
    (fun s t => finiteCharacterMass (F s) H β (t+u))
    (fun s _ => (finiteCharacterMass_continuous (F s) H β).comp
      (continuous_id.add continuous_const))]
  calc
    _ ≤ ∑ s ∈ U.powerset, 2*C*(1+(Z:ℝ)/T)*E s*H.card :=
      Finset.sum_le_sum (fun s _ => hrow s)
    _ = 2*C*(1+(Z:ℝ)/T)*(∑ s ∈ U.powerset, E s)*H.card := by
      rw [Finset.mul_sum,Finset.sum_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left
        (weighted_divisor_row_energy S U β hU (fun b hb => (hS b hb).1)) (by positivity)

end CubicFirstMoment

end

end OAI
