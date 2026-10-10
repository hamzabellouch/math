import OAI.NumberTheory.CubicMoment.Estimates.PrimeWeightVariation

namespace OAI

/-! A rescaled, Mellin-twisted prime estimate derived from the precise
published unweighted Siegel–Walfisz input. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma continuous_zero_on_lower_closed {w : ℝ → ℂ} (hw : Continuous w)
    (hlo : ∀ x, x < 1 → w x = 0) {x : ℝ} (hx : x ≤ 1) : w x = 0 := by
  have hc : closure (Iio (1:ℝ)) ⊆ {x | w x = 0} :=
    closure_minimal (fun x hx => hlo x hx) (isClosed_eq hw continuous_const)
  apply hc
  simpa only [closure_Iio,mem_Iic] using hx

def smoothPrimeCharacterSum (R Y : ℝ) (w : ℝ → ℂ) (χ : Eisenstein → ℂ) (u : ℝ) : ℂ :=
  ∑ p ∈ primeCutoff (R*Y), w (norm p/Y)*mellinPhase u (norm p)*χ p

lemma smoothPrimeCharacterSum_eq_interval {R Y : ℝ} (hY : 0 < Y)
    {w : ℝ → ℂ} (hw : Continuous w) (hlo : ∀ x, x < 1 → w x = 0)
    (χ : Eisenstein → ℂ) (u : ℝ) :
    smoothPrimeCharacterSum R Y w χ u =
      ∑ p ∈ (primeCutoff (R*Y)).filter (fun p => Y < norm p),
        (w (norm p/Y)*mellinPhase u (norm p))*χ p := by
  unfold smoothPrimeCharacterSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : Y < norm p
  · simp only [ite_eq_left hp]
  · have hz : w (norm p/Y) = 0 := continuous_zero_on_lower_closed hw hlo
      ((div_le_one hY).mpr (le_of_not_gt hp))
    simp only [ite_eq_right hp,hz,zero_mul]

theorem scaled_cubic_prime_bound (hSW : CubicPrimeSiegelWalfisz)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ (Y R M B : ℝ) (w : ℝ → ℂ),
      X₀ ≤ Y → 1 ≤ R → 0 ≤ M → 0 ≤ B → ContDiff ℝ ∞ w →
      (∀ x, x < 1 → w x = 0) → (∀ x, ‖w x‖ ≤ M) →
      (∀ x, 0 < x → ‖deriv w x‖*x ≤ B) →
      ∀ (q₁ q₂ : Eisenstein), primary q₁ → primary q₂ → Squarefree q₁ → Squarefree q₂ →
      IsCoprime q₁ q₂ → MixedCubicNonprincipal q₁ q₂ →
      norm (q₁*q₂) ≤ (Real.log Y)^A → ∀ u : ℝ,
      ‖smoothPrimeCharacterSum R Y w (mixedCubic q₁ q₂) u‖ ≤
        (C*(R*Y)/(Real.log Y)^D)*(2*M+(R-1)*(B+M*|u|)) := by
  obtain ⟨C,X₀,hC,hX₀,hbound⟩ := weighted_cubic_prime_bound hSW A D hA hD
  refine ⟨C,X₀,hC,hX₀,?_⟩
  intro Y R M B w hYX hR hM hB hw hlo hwm hwd q₁ q₂ h₁ h₂ hs₁ hs₂ hcop hnon hcon u
  have hY : 0 < Y := zero_lt_one.trans (hX₀.trans_le hYX)
  have hYR : Y ≤ R*Y := by nlinarith
  obtain ⟨hdiff,hderiv,hvar⟩ := rescaled_mellin_variation hw hY hR hM hB hwm hwd u
  rw [smoothPrimeCharacterSum_eq_interval hY hw.continuous hlo]
  exact (hbound Y (R*Y) hYX hYR q₁ q₂ h₁ h₂ hs₁ hs₂ hcop hnon hcon
    (fun t => w (t/Y)*mellinPhase u t) hdiff hderiv).trans
      (mul_le_mul_of_nonneg_left hvar
        (div_nonneg (mul_nonneg hC.le (mul_nonneg (zero_le_one.trans hR) hY.le))
          (Real.rpow_nonneg (Real.log_nonneg (le_of_lt (hX₀.trans_le hYX))) _)))

end CubicFirstMoment

end

end OAI
