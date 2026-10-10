import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeMellinEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.StructuredHeightContinuity

namespace OAI

/-! A polynomial envelope for the actual angular height mass, uniform
in height, angular index, numerator and exclusions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullStructuredAngularSum_norm_le_l1 (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (h v e : Eisenstein) (ℓ : ℤ) (u : ℝ) :
    ‖fullStructuredAngularSum R h v e ℓ u W X‖ ≤
      ∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖ := by
  have he : fullStructuredAngularSum R h v e ℓ u W X =
      ∑ b ∈ fullSquarefreePrimeSupport R W X e, fullPrimeCoefficient R W X b*
        (cubicSymbol b (v*h)*theta ℓ b*mellinPhase u (norm b)) := by
    calc
      _ = ∑ b ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter (fun b => IsCoprime b e),
          fullPrimeCoefficient R W X b*(cubicSymbol b (v*h)*theta ℓ b*mellinPhase u (norm b)) := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := fullPrimeCoefficient_sum_squarefree R W X e _
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  have hp := (fullSquarefreePrimeSupport_primary R W X e hb).1
  rw [norm_mul,norm_mul,norm_mul,norm_theta (primary_ne_zero hp),mellinPhase_norm,mul_one,mul_one]
  exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one hp _)

theorem logarithmic_full_height_envelope {R : ℝ} (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0) :
    ∃ (K : ℝ) (A : ℕ), 0 ≤ K ∧ ∀ (r : γ) (X : ι → ℝ), 1 ≤ L r →
      (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      ∀ (H : Finset Eisenstein) (v e : Eisenstein) (ℓ : ℤ) (u t : ℝ),
      fullStructuredHeightMass R H v e ℓ u (W r) X t ≤
        K*(H.card:ℝ)*(L r)^2*(1+Real.log (L r))^A := by
  obtain ⟨C,A,hC,henergy⟩ := logarithmic_full_coefficient_energy hW hR hlo hhi
  refine ⟨18*R^Fintype.card ι*C,A,by positivity,?_⟩
  intro r X hL hX hprod H v e ℓ u t
  have hl := fullPrimeCoefficient_l1_square (zero_le_one.trans hR) (W r) X
    (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) e
  rw [hprod] at hl
  have hl' := hl.trans (mul_le_mul_of_nonneg_left (henergy r X hL hX hprod) (by positivity))
  calc
    _ ≤ ∑ _h ∈ H, (∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
        ‖fullPrimeCoefficient R (W r) X b‖)^2 := by
      apply Finset.sum_le_sum
      intro h _
      exact pow_le_pow_left₀ (_root_.norm_nonneg _)
        (fullStructuredAngularSum_norm_le_l1 R (W r) X h v e ℓ (t+u)) 2
    _ = (H.card:ℝ)*(∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
        ‖fullPrimeCoefficient R (W r) X b‖)^2 := by simp
    _ ≤ (H.card:ℝ)*(18*(R^Fintype.card ι*L r)*(C*L r*(1+Real.log (L r))^A)) :=
      mul_le_mul_of_nonneg_left hl' (Nat.cast_nonneg _)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
