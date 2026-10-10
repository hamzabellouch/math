import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUniformMean
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUniformNegativeMean

namespace OAI

/-! Both actual angular height dyads, uniformly in the smooth family. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem UniformLogWeights.cubicTheta_completed_signed_angular_mean
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y X T : ℝ, 1 ≤ Y → 0 < X → 1 ≤ T →
      norm r ≤ Y^B → T ≤ Y^B → Y^(-B) ≤ X → X ≤ Y^B →
      ((∫ t in -(2*T)..-T, ‖metaplecticHeightCompleted r ℓ (W i) X t‖)+
        (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ (W i) X t‖))/T ≤
          K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  obtain ⟨C,hC,hpositive⟩ :=
    h.cubicTheta_completed_angular_mean hMV hM hℓ hη hB
  obtain ⟨D,hD,hnegative⟩ :=
    h.cubicTheta_completed_negative_angular_mean hMV hM hℓ hη hB
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro i r hr hsr Y X T hY hX hT hRY hTY hYX hXY
  have hp := hpositive i r hr hsr Y X T hY hX hT hRY hTY hYX hXY
  have hn := hnegative i r hr hsr Y X T hY hX hT hRY hTY hYX hXY
  have he := intervalIntegral.integral_comp_neg (a := T) (b := 2*T)
    (fun t : ℝ => ‖metaplecticHeightCompleted r ℓ (W i) X t‖)
  rw [←he,add_div]
  calc
    _ ≤ D*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T+
        C*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := add_le_add hn hp
    _ = _ := by ring


end CubicFirstMoment

end

end OAI
