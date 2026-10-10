import OAI.NumberTheory.CubicMoment.Transform.MetaplecticSelectedOuter
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShortLogInverse

namespace OAI

/-! The actual nonzero-angular theta formula supplies this central estimate. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem LogarithmicWeightFamily.cubicTheta_selected_short
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {ε b : ℝ} (hε : 0 < ε) (hb : 0 ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X N U C : ℝ),
      1 ≤ X → 0 ≤ N → 0 ≤ C →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ norm r ≤ N) →
      (∀ r ∈ S, Y (w r) ≤ X ∧ (Y (w r))^(-b) ≤ U ∧ U ≤ (Y (w r))^b ∧
        C ≤ (Y (w r))^b ∧ norm r ≤ (Y (w r))^b) →
      ‖∑ r ∈ S, α r*metaplecticShortCompletionError r ℓ (W (w r)) U C‖ ≤
        K*X^ε*Real.sqrt N*C^(3/2:ℝ)*(∑ r ∈ S, ‖α r‖) := by
  obtain ⟨K,hK,hbound⟩ := hW.cubicTheta_short_completion_error hℓ hε hb
  refine ⟨K,hK,?_⟩
  intro w S α X N U C _hX _hN hC hS hY
  have hbnd (r : Eisenstein) (hr : r ∈ S) :
      ‖metaplecticShortCompletionError r ℓ (W (w r)) U C‖ ≤
        K*X^ε*Real.sqrt N*C^(3/2:ℝ) := by
    obtain ⟨hp,hs,hn⟩ := hS r hr
    obtain ⟨hYX,hlo,hhi,hCY,hrY⟩ := hY r hr
    apply (hbound (w r) r hp hs U C hlo hhi hC hCY hrY).trans
    have hy := Real.rpow_le_rpow (zero_lt_one.trans_le (hW.length_one (w r))).le hYX hε.le
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hC _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hy hK) (Real.sqrt_le_sqrt hn)
      (Real.sqrt_nonneg _) (by positivity)
  calc
    _ ≤ ∑ r ∈ S, ‖α r‖*‖metaplecticShortCompletionError r ℓ (W (w r)) U C‖ := by
      simpa only [norm_mul] using norm_sum_le S
        (fun r => α r*metaplecticShortCompletionError r ℓ (W (w r)) U C)
    _ ≤ ∑ r ∈ S, ‖α r‖*(K*X^ε*Real.sqrt N*C^(3/2:ℝ)) :=
      Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hbnd r hr) (_root_.norm_nonneg _))
    _ = _ := by rw [←Finset.sum_mul]; ring

end CubicFirstMoment

end

end OAI
