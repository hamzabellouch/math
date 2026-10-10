import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCharacterRows
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedLargeDivisorMass
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedMellinRows
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedLargeDivisorPower
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedLargeDivisorMass
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorPowers

namespace OAI

/-! At the fixed cutoff b^(1/8), the actual large-divisor rows save
a fixed power uniformly in the ambient set of primes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_large_divisor_power_mass (ℓ : ℤ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X w z l b u M B : ℝ)
      (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop)
      (e : Eisenstein) (U H : Finset Eisenstein),
      1 ≤ b → 1 ≤ B → B ≤ b^(3/5:ℝ) → (∀ p ∈ U, primaryPrime p) →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        ‖angularStoppedRowCoefficient ℓ X w z u W selected n‖ ≤ M) →
      (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B) →
      (∑ s ∈ U.powerset.filter
          (fun s => b^(1/8:ℝ) < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ b),
        ∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter
            (fun n => (∏ p ∈ s,p) ∣ n),
          angularStoppedRowCoefficient ℓ X w z u W selected n*cubicSymbol n v‖^2) ≤
      K*B^(1/3:ℝ)*b^(2-1/20:ℝ)*M^2 := by
  obtain ⟨K,hK,hbound⟩ := angular_stopped_large_divisor_mass ℓ (ι := ι)
    (show (0:ℝ) < 1/1000 by norm_num) (show (0:ℝ) < 1/12 by norm_num)
  let C₁ := ∑' n : Eisenstein, norm n^(-(1+1/12:ℝ))
  let C₂ := ∑' n : Eisenstein, norm n^(-(5/3:ℝ))
  let C₃ := ∑' n : Eisenstein, norm n^(-(3/2:ℝ))
  have hC₁ : 0 ≤ C₁ := tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _)
  have hC₂ : 0 ≤ C₂ := tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _)
  have hC₃ : 0 ≤ C₃ := tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _)
  let C := (2:ℝ)^(1/1000:ℝ)*(C₁+C₂+C₃)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨K*(C+1),by positivity,?_⟩
  intro X w z l b u M B W selected e U H hb hB hBb hU hcoeff hH
  have hbp : 0 < b := zero_lt_one.trans_le hb
  have hm := hbound X w z l b u M B (b^(1/8:ℝ)) W selected e U H
    hbp hB (Real.rpow_pos_of_pos hbp _) hU hcoeff hH
  have hs := stopped_large_divisor_power hb (zero_lt_one.trans_le hB) hBb hC₁ hC₂ hC₃
  apply hm.trans
  calc
    _ = (K*M^2)*((2*B*b)^(1/1000:ℝ)*(
        B*b*b^(1/12:ℝ)*C₁+B^(2/3:ℝ)*b^(5/3:ℝ)*C₂+
        B^(1/3:ℝ)*b^2*(b^(1/8:ℝ))^(-(1/2:ℝ))*C₃)) := by
      dsimp [C₁,C₂,C₃]; ring
    _ ≤ (K*M^2)*(C*B^(1/3:ℝ)*b^(2-1/20:ℝ)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (K*M^2)*((C+1)*B^(1/3:ℝ)*b^(2-1/20:ℝ)) := by gcongr; linarith
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
