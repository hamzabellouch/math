import OAI.NumberTheory.CubicMoment.Estimates.PrimaryNormMultiplicity
import OAI.NumberTheory.CubicMoment.Estimates.HeightAveraging
import OAI.NumberTheory.CubicMoment.Estimates.HeightMeanSquare

namespace OAI

/-! Ordinary height means for arbitrary primary coefficient supports,
including sharp norm cells and every translated angular mode. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma continuous_finite_character_height (B : Finset Eisenstein)
    (β : Eisenstein → ℂ) (h : Eisenstein) (ℓ : ℤ) (u : ℝ) :
    Continuous (fun t => ∑ b ∈ B, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)) := by
  apply continuous_finsetSum
  intro b hb
  change Continuous (fun t => (β b*cubicSymbol b h*theta ℓ b)*normTwist (t+u) b)
  exact continuous_const.mul ((continuous_normTwist b).comp (continuous_id.add continuous_const))

/-- Exact norm-fiber cost for the finite family. Character factors can
only reduce the coefficient energy. -/
theorem finite_character_height_mean {C M T : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hM : 0 ≤ M) (hT : 0 < T)
    (B H : Finset Eisenstein) (β : Eisenstein → ℂ) (Z : ℕ)
    (hB : ∀ b ∈ B, primary b)
    (hZ : ∀ b ∈ B, normNat b ∈ Finset.Icc 1 Z)
    (hmult : ∀ n ∈ Finset.Icc 1 Z, ((B.filter (fun b => normNat b = n)).card:ℝ) ≤ M)
    (ℓ : ℤ) (u : ℝ) :
    dyadicHeightMean (fun t => ∑ h ∈ H,
      ‖∑ b ∈ B, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      2*C*(1+(Z:ℝ)/T)*M*H.card*∑ b ∈ B, ‖β b‖^2 := by
  have hc (h : Eisenstein) := (continuous_finite_character_height B β h ℓ u).norm.pow 2
  rw [dyadicHeightMean_sum H (fun h t =>
    ‖∑ b ∈ B, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2)
      (fun h _ => hc h)]
  have hrow (h : Eisenstein) :
      dyadicHeightMean (fun t =>
        ‖∑ b ∈ B, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      2*C*(1+(Z:ℝ)/T)*M*∑ b ∈ B, ‖β b‖^2 := by
    have hm := fixedAngular_translated_dyadicMeanSquare hMV hC B
      (fun b => β b*cubicSymbol b h) Z M hZ
      (fun b hb => primary_ne_zero (hB b hb)) hmult ℓ u hT
    apply hm.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro b hb
    apply pow_le_pow_left₀ (_root_.norm_nonneg _) _ 2
    rw [norm_mul]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hB b hb) h)
  calc
    _ ≤ ∑ _h ∈ H, 2*C*(1+(Z:ℝ)/T)*M*∑ b ∈ B, ‖β b‖^2 :=
      Finset.sum_le_sum (fun h _ => hrow h)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- With no fixed number of prime factors, the proved primary norm-fiber
bound gives an arbitrarily small length loss, uniformly in all twists. -/
theorem arbitrary_primary_height_mean {C ε : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (B H : Finset Eisenstein) (β : Eisenstein → ℂ) (Z : ℕ),
      (∀ b ∈ B, primary b) → (∀ b ∈ B, normNat b ∈ Finset.Icc 1 Z) →
      ∀ (ℓ : ℤ) (u T : ℝ), 0 < T →
      dyadicHeightMean (fun t => ∑ h ∈ H,
        ‖∑ b ∈ B, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
        2*C*D*(1+(Z:ℝ)/T)*(Z:ℝ)^ε*H.card*∑ b ∈ B, ‖β b‖^2 := by
  obtain ⟨D,hD,hfiber⟩ := primary_norm_fiber_length_bound hε
  refine ⟨D,hD,?_⟩
  intro B H β Z hB hZ ℓ u T hT
  have hm := finite_character_height_mean hMV hC
    (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg Z) _)) hT B H β Z hB hZ
    (hfiber B hB Z) ℓ u
  convert hm using 1
  ring

end CubicFirstMoment

end

end OAI
