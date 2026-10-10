import OAI.NumberTheory.CubicMoment.Estimates.LowProfilePoissonTotal
import OAI.NumberTheory.CubicMoment.Estimates.SmallBCoprimeDispersion

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment.ProfileControl

theorem low_coprime_dispersion_height_log_saving (hpnt : PrimaryPrimePNT) (k : ℕ)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (A T M u : ℝ), 65536 ≤ (Z:ℝ) → 16 ≤ (Z:ℝ)^(3/4:ℝ) → 0 ≤ M →
      (1+Real.log Z)^Ct ≤ T → (Z:ℝ)^(3/2:ℝ) ≤ A →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ (Z:ℝ)/2 ≤ norm b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t => ‖coprimeDispersionGram S β (u+t) P.V A‖) T ≤
        (K*P.cost)*M^2*A^(2/3:ℝ)*(Z:ℝ)^(5/3:ℝ)/(1+Real.log Z)^k := by
  obtain ⟨K₀,Ct,hK₀,hbound₀⟩ := low_poisson_total_height_log_saving hpnt k hMV hC hHuxley
  refine ⟨K₀,Ct,hK₀,?_⟩
  intro P S β Z A T M u hZ hlarge hM hT hAlo hS hβ
  let K := K₀*P.cost
  have hK : 0 < K := mul_pos hK₀ P.cost_pos
  have hbound := hbound₀ P
  have hA : 0 < A := (Real.rpow_pos_of_pos (by linarith : 0 < (Z:ℝ)) _).trans_le hAlo
  have hp : ∀ b ∈ S, primary b ∧ Squarefree b ∧ b ≠ 1 := by
    intro b hb
    refine ⟨(hS b hb).1,(hS b hb).2.1,?_⟩
    intro he
    have hn := (hS b hb).2.2.1
    rw [he,norm_one_eq] at hn
    linarith
  have he (t : ℝ) := coprimeDispersionGram_eq_poisson_series S hp β (u+t) P.V P.compact P.smooth hA
  simp_rw [he]
  exact hbound S frequencyDyad β Z A T M u hZ hlarge hM hT hAlo hS hβ (fun _ => Finset.Subset.refl _)


end CubicFirstMoment.ProfileControl

end

end OAI
