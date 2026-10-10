import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailPoissonTotal
import OAI.NumberTheory.CubicMoment.Estimates.CoprimePoissonSeries

namespace OAI

/-! The arbitrary-coefficient small-B estimate for the original
coprime dispersion Gram form, obtained from the complete Poisson series. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem primeGroupTail_coprime_dispersion_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (A T u : ℝ), 4 ≤ (Z:ℝ) → 16 ≤ (Z:ℝ)^(19/20:ℝ) →
      (Z:ℝ)^(1/50:ℝ) ≤ T → (Z:ℝ)^(27/25:ℝ) ≤ A →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ (Z:ℝ)/2 ≤ norm b ∧ norm b ≤ (Z:ℝ)) →
      dyadicHeightMean (fun t => ‖coprimeDispersionGram S β (u+t) V A‖) T ≤
        K*A^(2/3:ℝ)*(Z:ℝ)^(2/3-1/40000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hbound⟩ := primeGroupTail_poisson_total_height_power hMV hC hHuxley V hV hV'
  refine ⟨K,hK,?_⟩
  intro S β Z A T u hZ hlarge hT hAlo hS
  have hA : 0 < A := (Real.rpow_pos_of_pos (by linarith : 0 < (Z:ℝ)) _).trans_le hAlo
  have hp : ∀ b ∈ S, primary b ∧ Squarefree b ∧ b ≠ 1 := by
    intro b hb
    refine ⟨(hS b hb).1,(hS b hb).2.1,?_⟩
    intro he
    have hn := (hS b hb).2.2.1
    rw [he,norm_one_eq] at hn
    linarith
  have he (t : ℝ) := coprimeDispersionGram_eq_poisson_series S hp β (u+t) V hV hV' hA
  simp_rw [he]
  exact hbound S frequencyDyad β Z A T u hZ hlarge hT hAlo hS (fun _ => Finset.Subset.refl _)

end CubicFirstMoment

end

end OAI
