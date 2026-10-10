import OAI.NumberTheory.CubicMoment.Estimates.WeightedLowHeightBlocks
import OAI.NumberTheory.CubicMoment.Estimates.WeightedDivisorEnergy
import OAI.NumberTheory.CubicMoment.Estimates.DivisorCharacterMass

namespace OAI

/-! The full coprimality expansion at low height, with its divisor cost
retained in the actual third weighted coefficient energy. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem divisor_noncube_low_height_blocks
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B V T u : ℝ), 65536 ≤ (Z:ℝ) → 0 ≤ B → 0 < V → 0 < T →
      (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(3/4:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h) →
      dyadicHeightMean (fun t => divisorCharacterMass S H U β (t+u)) T ≤
        K*B^(1/3:ℝ)*(∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2)*
          ((1+(Z:ℝ)/T)*V+((largeCoreDyadicIndices V B).card:ℝ)*
            ((Z:ℝ)*(V/5832)^(-(1/4:ℝ))+(Z:ℝ)^(1-1/20000:ℝ))) := by
  obtain ⟨K,hK,hbound⟩ := smallB_noncube_weighted_blocks hMV hC hHuxley
  refine ⟨K,hK,?_⟩
  intro S H U β Z B V T u hZ hB hV hT hU hS hsize hH
  let F := fun s : Finset Eisenstein => S.filter (fun b => (∏ p ∈ s, p) ∣ b)
  let E₄ := fun s => ∑ b ∈ F s, (4:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2
  let E₀ := fun s => ∑ b ∈ F s, ‖β b‖^2
  let E₈ := ∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2
  let A := (1+(Z:ℝ)/T)*V
  let R := ((largeCoreDyadicIndices V B).card:ℝ)*
    ((Z:ℝ)*(V/5832)^(-(1/4:ℝ))+(Z:ℝ)^(1-1/20000:ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hrow (s : Finset Eisenstein) :
      dyadicHeightMean (fun t => finiteCharacterMass (F s) H β (t+u)) T ≤
        K*B^(1/3:ℝ)*(A*E₄ s+R*E₀ s) := by
    have hh := hbound (F s) H β Z B V T u 0 hZ hB hV hT
      (fun b hb => hS b (Finset.mem_filter.mp hb).1) hsize hH
    simp only [theta_zero,mul_one] at hh
    convert hh using 1 <;> dsimp [finiteCharacterMass,A,R,E₄,E₀]
    ring
  have hfour : (∑ s ∈ U.powerset, E₄ s) ≤ E₈ :=
    weighted_divisor_row_energy S U β hU (fun b hb => (hS b hb).1)
  have hzero : (∑ s ∈ U.powerset, E₀ s) ≤ E₈ :=
    ordinary_divisor_row_energy S U β hU (fun b hb => (hS b hb).1)
  unfold divisorCharacterMass
  rw [dyadicHeightMean_sum U.powerset
    (fun s t => finiteCharacterMass (F s) H β (t+u))
    (fun s _ => (finiteCharacterMass_continuous (F s) H β).comp (continuous_id.add continuous_const))]
  calc
    _ ≤ ∑ s ∈ U.powerset, K*B^(1/3:ℝ)*(A*E₄ s+R*E₀ s) :=
      Finset.sum_le_sum (fun s _ => hrow s)
    _ = K*B^(1/3:ℝ)*(A*(∑ s ∈ U.powerset, E₄ s)+R*(∑ s ∈ U.powerset, E₀ s)) := by
      simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ K*B^(1/3:ℝ)*(A*E₈+R*E₈) := by gcongr
    _ = _ := by dsimp [A,R,E₈]; ring

end CubicFirstMoment

end

end OAI
