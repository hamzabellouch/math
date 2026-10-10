import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCompletedShort

namespace OAI

/-! Reflection of the interval reduces the negative short-polynomial
mean to the already proved arbitrary-shift primal mean. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma integral_reflected_height (f : ℝ → ℝ) (T : ℝ) :
    (∫ t in T..2*T, f (-t)) = (∫ t in T..2*T, f (t-3*T)) := by
  let g := fun t : ℝ => f (t-3*T)
  have he := intervalIntegral.integral_comp_sub_left (a := T) (b := 2*T) g (3*T)
  rw [show 3*T-2*T = T by ring,show 3*T-T = 2*T by ring] at he
  have hg : (fun t => g (3*T-t)) = (fun t => f (-t)) := by
    funext t
    dsimp [g]
    congr 1
    ring
  rw [hg] at he
  exact he

theorem metaplectic_completed_negative_short_mean
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hc : Continuous W)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : Eisenstein, primary r →
      ∀ (ℓ : ℤ) (Y X T : ℝ), 1 ≤ Y → 0 < X → 1 ≤ T → X ≤ Y^B →
      X ≤ Real.sqrt (norm r)*T^2 →
      (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ W X (-t)‖)/T ≤
        K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  obtain ⟨K,hK,hbound⟩ := metaplectic_completed_short_mean hMV hC W hW hc hη hB
  refine ⟨K,hK,?_⟩
  intro r hr ℓ Y X T hY hX hT hXY hshort
  rw [integral_reflected_height (fun t => ‖metaplecticHeightCompleted r ℓ W X t‖) T]
  simpa only [sub_eq_add_neg] using hbound r hr ℓ Y X T (-(3*T)) hY hX hT hXY hshort

end CubicFirstMoment

end

end OAI
