import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUniformLong
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUniformShort
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompletedMean

namespace OAI

/-! The actual fixed nonzero-angular height mean across both ranges.
The fixed dilation is absorbed in constants and the existing polynomial
scale range; no metaplectic Voronoi premise is used. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

theorem UniformLogWeights.cubicTheta_completed_angular_mean
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0≤M)
    {ι : Type*} {W : ι→ℝ→ℂ} (hW : UniformLogWeights W) {ℓ : ℤ} (hℓ : ℓ≠0)
    {η B : ℝ} (hη : 0<η) (hB : 0≤B) :
    ∃ K : ℝ, 0≤K ∧ ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y X T : ℝ, 1≤Y → 0<X → 1≤T →
      norm r≤Y^B → T≤Y^B → Y^(-B)≤X → X≤Y^B →
      (∫ t in T..2*T,‖metaplecticHeightCompleted r ℓ (W i) X t‖)/T≤
        K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  obtain ⟨C,hC,hshort⟩ := hW.cubicTheta_completed_short_mean hMV hM hη hB
  obtain ⟨m,D,hm,hD,hlong⟩ := hW.cubicTheta_completed_dilated_long_mean hMV hM hℓ
    hη (show 0≤B+1 by linarith)
  have hGammaMinus := angularGammaQuotientStripBound_proved (metaplecticAngularShift ℓ-1/6)
    (-((m:ℝ)-1/2)) (by linarith [metaplecticAngularShift_nonneg ℓ])
  have hGammaPlus := angularGammaQuotientStripBound_proved (metaplecticAngularShift ℓ+1/6)
    (-((m:ℝ)-1/2)) (by linarith [metaplecticAngularShift_nonneg ℓ])
  refine ⟨C+D*(729:ℝ)^η,by positivity,?_⟩
  intro i r hr hsr Y X T hY hX hT hRY hTY hYX hXY
  have hnr := norm_nonneg r
  have hcommon : 0≤Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by positivity
  by_cases hs : X≤729*Real.sqrt (norm r)*T^2
  · have hh := hshort i r hr ℓ Y X T 0 hY hX hT hXY hs
    simp only [add_zero] at hh
    apply hh.trans
    nlinarith only [mul_nonneg (mul_nonneg hD (Real.rpow_nonneg (by norm_num : (0:ℝ)≤729) η)) hcommon]
  · have hZ : 1≤729*Y := by linarith
    have hlong' : Real.sqrt (norm r)*T^2≤X/729 := by linarith
    have hdown : (729*Y)^(-(B+1))≤X/729 :=
      (cubicTheta_dilated_lower_scale hY hB).trans (div_le_div_of_nonneg_right hYX (by norm_num))
    have hu := cubicTheta_dilated_upper_scale hY hB
    have hh := hlong i r hr hsr (729*Y) (X/729) T hZ (by positivity) hT
      (hRY.trans hu) (hTY.trans hu) hdown hlong' hGammaMinus hGammaPlus
    have hx : 729*(X/729)=X := by ring
    rw [hx,Real.mul_rpow (by norm_num : (0:ℝ)≤729) (by linarith : 0≤Y)] at hh
    have hsmall : Real.sqrt (X/729)≤Real.sqrt X := Real.sqrt_le_sqrt (by linarith)
    calc
      _ ≤ D*Real.sqrt (X/729)*((729:ℝ)^η*Y^η)*norm r^(1/4:ℝ)*Real.sqrt T := hh
      _ ≤ D*Real.sqrt X*((729:ℝ)^η*Y^η)*norm r^(1/4:ℝ)*Real.sqrt T := by gcongr
      _ ≤ _ := by nlinarith only [mul_nonneg hC hcommon]

end CubicFirstMoment

end

end OAI
