import OAI.NumberTheory.CubicMoment.Estimates.LowVarianceRemainder
import OAI.NumberTheory.CubicMoment.Estimates.ThinZeroMode

namespace OAI

/-! The derivative family is selected independently of the requested
logarithmic saving. This order is needed for shrinking norm cutoffs. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap
namespace CubicFirstMoment

theorem low_variance_remainder_finite_seminorm
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ I : Finset (ℕ × ℕ), ∀ j : ℕ,
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
        (S : Finset Eisenstein) (β : Eisenstein → ℂ) (Z A T M u : ℝ),
      (65536:ℝ)^2 ≤ Z → Z^(3/2:ℝ) ≤ A → (1+Real.log Z)^Ct ≤ T → 0 ≤ M →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t =>
        ‖smoothedDispersionVariance S β (u+t) V A-varianceZeroMode S β V A‖) T ≤
        K*(1+(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
          (normProfileFourierSchwartz V hV hV'))*
          M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨I,D,hD,hprofile⟩ := exists_poissonProfileBudget_control
  refine ⟨I,?_⟩
  intro j
  obtain ⟨K,Ct,hK,hbound⟩ := ProfileControl.low_variance_remainder_height_log_saving
    hpnt j hMV hC hHuxley
  refine ⟨K*(1+D),Ct,by positivity,?_⟩
  intro V hV hV' S β Z A T M u hZ hA hT hM hS hβ
  have hZ1 : 1 ≤ Z := by nlinarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hA0 : 0 ≤ A := (Real.rpow_nonneg (by linarith : 0 ≤ Z) _).trans hA
  obtain ⟨P,hPV,hP⟩ := hprofile V hV hV'
  have hb := hbound P S β Z A T M u hZ hA hT hM hS hβ
  rw [hPV] at hb
  let N := (I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
    (normProfileFourierSchwartz V hV hV')
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hc : K*P.cost ≤ K*(1+D)*(1+N) := by
    have hp : P.cost ≤ (1+D)*(1+N) := by nlinarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hK.le
  apply hb.trans
  gcongr

end CubicFirstMoment

end

end OAI
