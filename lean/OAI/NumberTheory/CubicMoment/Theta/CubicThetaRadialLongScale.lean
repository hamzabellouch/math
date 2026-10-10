import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialLong
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialNegativeLong
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompletedMean

namespace OAI

/-! Put the two actual radial remainder means back on the original scale.
The fixed factor 729 changes only the uniform constant. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

theorem UniformLogWeights.cubicTheta_radial_remainder_long_mean
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι→ℝ→ℂ} (h : UniformLogWeights W)
    {η B : ℝ} (hη : 0<η) (hB : 0 ≤ B) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ i r,primary r → Squarefree r →
      ∀ Y X T : ℝ,1 ≤ Y → 0<X → 1 ≤ T → norm r ≤ Y^B → T ≤ Y^B → Y^(-B) ≤ X →
      729*Real.sqrt (norm r)*T^2 ≤ X →
      (∫ t in T..2*T,‖cubicThetaRadialHeightRemainder r (W i) X t‖)/T ≤ 
        K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  obtain ⟨m,D,hm,hD,hlong⟩ := h.cubicTheta_radial_remainder_dilated_long_mean
    hMV hM hη (show 0 ≤ B+1 by linarith)
  have hgm := angularGammaQuotientStripBound_proved (metaplecticAngularShift 0-1/6)
    (-((m:ℝ)-1/2)) (by norm_num [metaplecticAngularShift])
  have hgp := angularGammaQuotientStripBound_proved (metaplecticAngularShift 0+1/6)
    (-((m:ℝ)-1/2)) (by norm_num [metaplecticAngularShift])
  refine ⟨D*(729:ℝ)^η,by positivity,?_⟩
  intro i r hr hsr Y X T hY hX hT hRY hTY hYX hlongX
  have hZ : 1 ≤ 729*Y := by linarith
  have hlong' : Real.sqrt (norm r)*T^2 ≤ X/729 := by linarith
  have hdown : (729*Y)^(-(B+1)) ≤ X/729 :=
    (cubicTheta_dilated_lower_scale hY hB).trans (div_le_div_of_nonneg_right hYX (by norm_num))
  have hu := cubicTheta_dilated_upper_scale hY hB
  have hh := hlong i r hr hsr (729*Y) (X/729) T hZ (by positivity) hT
    (hRY.trans hu) (hTY.trans hu) hdown hlong' hgm hgp
  rw [show 729*(X/729)=X by ring,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 729) (by linarith : 0 ≤ Y)] at hh
  have hnr := norm_nonneg r
  have hsmall : Real.sqrt (X/729) ≤ Real.sqrt X := Real.sqrt_le_sqrt (by linarith)
  calc
    _  ≤  D*Real.sqrt (X/729)*((729:ℝ)^η*Y^η)*norm r^(1/4:ℝ)*Real.sqrt T := hh
    _  ≤  D*Real.sqrt X*((729:ℝ)^η*Y^η)*norm r^(1/4:ℝ)*Real.sqrt T := by gcongr
    _ = _ := by ring

theorem UniformLogWeights.cubicTheta_radial_remainder_negative_long_mean
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M)
    {ι : Type*} {W : ι→ℝ→ℂ} (h : UniformLogWeights W)
    {η B : ℝ} (hη : 0<η) (hB : 0 ≤ B) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ i r,primary r → Squarefree r →
      ∀ Y X T : ℝ,1 ≤ Y → 0<X → 1 ≤ T → norm r ≤ Y^B → T ≤ Y^B → Y^(-B) ≤ X →
      729*Real.sqrt (norm r)*T^2 ≤ X →
      (∫ t in T..2*T,‖cubicThetaRadialHeightRemainder r (W i) X (-t)‖)/T ≤ 
        K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  obtain ⟨m,D,hm,hD,hlong⟩ := h.cubicTheta_radial_remainder_dilated_negative_long_mean
    hMV hM hη (show 0 ≤ B+1 by linarith)
  have hgm := angularGammaQuotientStripBound_proved (metaplecticAngularShift 0-1/6)
    (-((m:ℝ)-1/2)) (by norm_num [metaplecticAngularShift])
  have hgp := angularGammaQuotientStripBound_proved (metaplecticAngularShift 0+1/6)
    (-((m:ℝ)-1/2)) (by norm_num [metaplecticAngularShift])
  refine ⟨D*(729:ℝ)^η,by positivity,?_⟩
  intro i r hr hsr Y X T hY hX hT hRY hTY hYX hlongX
  have hZ : 1 ≤ 729*Y := by linarith
  have hlong' : Real.sqrt (norm r)*T^2 ≤ X/729 := by linarith
  have hdown : (729*Y)^(-(B+1)) ≤ X/729 :=
    (cubicTheta_dilated_lower_scale hY hB).trans (div_le_div_of_nonneg_right hYX (by norm_num))
  have hu := cubicTheta_dilated_upper_scale hY hB
  have hh := hlong i r hr hsr (729*Y) (X/729) T hZ (by positivity) hT
    (hRY.trans hu) (hTY.trans hu) hdown hlong' hgm hgp
  rw [show 729*(X/729)=X by ring,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 729) (by linarith : 0 ≤ Y)] at hh
  have hnr := norm_nonneg r
  have hsmall : Real.sqrt (X/729) ≤ Real.sqrt X := Real.sqrt_le_sqrt (by linarith)
  calc
    _  ≤  D*Real.sqrt (X/729)*((729:ℝ)^η*Y^η)*norm r^(1/4:ℝ)*Real.sqrt T := hh
    _  ≤  D*Real.sqrt X*((729:ℝ)^η*Y^η)*norm r^(1/4:ℝ)*Real.sqrt T := by gcongr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
