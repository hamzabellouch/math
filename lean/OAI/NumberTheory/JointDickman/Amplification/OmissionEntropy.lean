import OAI.NumberTheory.JointDickman.Amplification.SubsetCountBounds
import OAI.NumberTheory.JointDickman.Amplification.PrefixOmissions

namespace OAI

/-! # Entropy cost of high-prime omissions -/

namespace JointDickman
open Finset Classical

/-- The bound uses an upper bound for the population size, so it applies
uniformly throughout a regularity window. -/
theorem subset_count_entropy_of_card_le (P : Finset ℕ) {θ m : ℝ}
    (hθ : 0 < θ) (hθhalf : θ ≤ 1/2) (hcard : (P.card : ℝ) ≤ m) :
    ((P.powerset.filter (fun A => (A.card : ℝ) ≤ θ*m)).card : ℝ) ≤
      Real.exp (m*Real.binEntropy θ) := by
  have hθ1 : θ < 1 := by linarith
  have h1θ : 0 < 1-θ := by linarith
  let t := Real.log (1-θ)-Real.log θ
  have ht : 0 ≤ t := sub_nonneg.mpr (Real.log_le_log hθ (by linarith))
  have he : Real.exp (-t) = θ/(1-θ) := by
    dsimp [t]
    rw [neg_sub,Real.exp_sub,Real.exp_log hθ,Real.exp_log h1θ]
  have hb : 1+Real.exp (-t) = (1-θ)⁻¹ := by rw [he]; field_simp; ring
  have hlog : Real.log (1+Real.exp (-t)) = -Real.log (1-θ) := by rw [hb,Real.log_inv]
  have hnon : 0 ≤ Real.log (1+Real.exp (-t)) :=
    Real.log_nonneg (by linarith [Real.exp_pos (-t)])
  have hp : (1+Real.exp (-t))^P.card =
      Real.exp ((P.card : ℝ)*Real.log (1+Real.exp (-t))) := by
    rw [Real.exp_nat_mul,Real.exp_log (by positivity)]
  calc
    _ ≤ Real.exp (t*(θ*m))*(1+Real.exp (-t))^P.card := subset_count_exp_bound P ht _
    _ = Real.exp (t*(θ*m)+(P.card : ℝ)*Real.log (1+Real.exp (-t))) := by rw [hp,Real.exp_add]
    _ ≤ Real.exp (t*(θ*m)+m*Real.log (1+Real.exp (-t))) :=
      Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_right hcard hnon])
    _ = _ := by
      rw [hlog]
      congr 1
      simp only [t,Real.binEntropy,Real.log_inv]
      ring

/-- On each endpoint the higher omissions cost an entropy exponent tending
to zero with τ. This statement keeps the exact real threshold 4τℓ. -/
theorem high_omission_count_bound (P : Finset ℕ) {τ ℓ : ℝ}
    (hτ : 0 < τ) (hτsmall : τ ≤ 1/100) (_hℓ : 0 ≤ ℓ)
    (hcard : (P.card : ℝ) ≤ (1/2+τ)*ℓ) :
    ((P.powerset.filter (fun A => (A.card : ℝ) ≤ 4*τ*ℓ)).card : ℝ) ≤
      Real.exp (((1/2+τ)*Real.binEntropy (4*τ/(1/2+τ)))*ℓ) := by
  have hd : 0 < (1/2 : ℝ)+τ := by linarith
  have hθ : 0 < 4*τ/((1/2 : ℝ)+τ) := div_pos (by positivity) hd
  have hh : 4*τ/((1/2 : ℝ)+τ) ≤ 1/2 := (div_le_iff₀ hd).mpr (by linarith)
  have hb := subset_count_entropy_of_card_le P hθ hh hcard
  have he : 4*τ/((1/2 : ℝ)+τ)*(((1/2 : ℝ)+τ)*ℓ) = 4*τ*ℓ := by field_simp
  rw [he] at hb
  calc
    _ ≤ Real.exp (((1/2+τ)*ℓ)*Real.binEntropy (4*τ/(1/2+τ))) := hb
    _ = _ := by congr 1; ring

end JointDickman

end OAI
