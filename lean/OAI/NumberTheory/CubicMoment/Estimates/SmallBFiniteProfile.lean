import OAI.NumberTheory.CubicMoment.Estimates.ProfileVarianceRemainder
import OAI.NumberTheory.CubicMoment.Estimates.ThinZeroMode

namespace OAI

/-! The profile derivative cost is chosen before the profile itself.
This is the quantitative form required by shrinking norm cells. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap
namespace CubicFirstMoment

theorem smallB_variance_remainder_finite_seminorm
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (I : Finset (ℕ × ℕ)) (K : ℝ), 0 < K ∧
      ∀ (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
        (S : Finset Eisenstein) (β : Eisenstein → ℂ) (Z A T u : ℝ),
      65536 ≤ Z → Z^(3/2:ℝ) ≤ A → Z^(1/50:ℝ) ≤ T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t =>
        ‖smoothedDispersionVariance S β (u+t) V A-varianceZeroMode S β V A‖) T ≤
        K*(1+(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
          (normProfileFourierSchwartz V hV hV'))*
          A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨I,D,hD,hprofile⟩ := exists_poissonProfileBudget_control
  obtain ⟨K,hK,hbound⟩ := ProfileControl.smallB_variance_remainder_height_power hMV hC hHuxley
  refine ⟨I,K*(1+D),by positivity,?_⟩
  intro V hV hV' S β Z A T u hZ hA hT hS
  obtain ⟨P,hPV,hP⟩ := hprofile V hV hV'
  have hb := hbound P S β Z A T u hZ hA hT hS
  rw [hPV] at hb
  let N := (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) (normProfileFourierSchwartz V hV hV')
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hc : K*P.cost ≤ K*(1+D)*(1+N) := by
    have hp : P.cost ≤ (1+D)*(1+N) := by nlinarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hK.le
  have hA0 : 0 ≤ A := (Real.rpow_nonneg (by linarith : 0 ≤ Z) (3/2:ℝ)).trans hA
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc
      (Real.rpow_nonneg hA0 _))
      (Real.rpow_nonneg (by linarith) _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end CubicFirstMoment

end

end OAI
