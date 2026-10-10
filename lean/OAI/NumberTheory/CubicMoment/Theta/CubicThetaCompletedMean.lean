import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompletedLong
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompletedShort
import OAI.NumberTheory.CubicMoment.Estimates.GammaQuotientGrowth

namespace OAI

/-! The actual fixed nonzero-angular height mean across both ranges.
The fixed dilation is absorbed in constants and the existing polynomial
scale range; no metaplectic Voronoi premise is used. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicTheta_dilated_lower_scale {Y B : ℝ} (hY : 1≤Y) (hB : 0≤B) :
    (729*Y)^(-(B+1))≤Y^(-B)/729 := by
  have hYp : 0<Y := zero_lt_one.trans_le hY
  have hZp : 0<729*Y := by positivity
  have hbase : Y≤729*Y := by linarith
  have hfirst : (729*Y)^(-B)≤Y^(-B) :=
    Real.rpow_le_rpow_of_nonpos hYp hbase (by linarith)
  have hsecond : (729*Y)^(-(1:ℝ))≤(729:ℝ)^(-(1:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by norm_num)
  calc
    _ = (729*Y)^(-B)*(729*Y)^(-(1:ℝ)) := by
      rw [←Real.rpow_add hZp]
      congr 1
      ring
    _ ≤ Y^(-B)*(729:ℝ)^(-(1:ℝ)) := mul_le_mul hfirst hsecond
      (Real.rpow_nonneg hZp.le _) (Real.rpow_nonneg hYp.le _)
    _ = _ := by norm_num [Real.rpow_neg_one,div_eq_mul_inv]

lemma cubicTheta_dilated_upper_scale {Y B : ℝ} (hY : 1≤Y) (hB : 0≤B) :
    Y^B≤(729*Y)^(B+1) := by
  have hZ : 1≤729*Y := by linarith
  exact (Real.rpow_le_rpow (by linarith) (by linarith) hB).trans
    (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))

theorem cubicTheta_completed_angular_mean
    {M : ℝ} (hMV : MontgomeryVaughanBound M) (hM : 0≤M)
    {ℓ : ℤ} (hℓ : ℓ≠0) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {η B : ℝ} (hη : 0<η) (hB : 0≤B) :
    ∃ K : ℝ, 0≤K ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ Y X T : ℝ, 1≤Y → 0<X → 1≤T →
      norm r≤Y^B → T≤Y^B → Y^(-B)≤X → X≤Y^B →
      (∫ t in T..2*T,‖metaplecticHeightCompleted r ℓ W X t‖)/T≤
        K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  obtain ⟨C,hC,hshort⟩ := cubicTheta_completed_short_mean hMV hM W hW hsm.continuous hη hB
  obtain ⟨m,D,hm,hD,hlong⟩ := cubicTheta_completed_dilated_long_mean hMV hM hℓ W hW hpos hsm
    hη (show 0≤B+1 by linarith)
  have hGammaMinus := angularGammaQuotientStripBound_proved (metaplecticAngularShift ℓ-1/6)
    (-((m:ℝ)-1/2)) (by linarith [metaplecticAngularShift_nonneg ℓ])
  have hGammaPlus := angularGammaQuotientStripBound_proved (metaplecticAngularShift ℓ+1/6)
    (-((m:ℝ)-1/2)) (by linarith [metaplecticAngularShift_nonneg ℓ])
  refine ⟨C+D*(729:ℝ)^η,by positivity,?_⟩
  intro r hr hsr Y X T hY hX hT hRY hTY hYX hXY
  have hnr := norm_nonneg r
  have hcommon : 0≤Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by positivity
  by_cases hs : X≤729*Real.sqrt (norm r)*T^2
  · have hh := hshort r hr ℓ Y X T 0 hY hX hT hXY hs
    simp only [add_zero] at hh
    apply hh.trans
    nlinarith only [mul_nonneg (mul_nonneg hD (Real.rpow_nonneg (by norm_num : (0:ℝ)≤729) η)) hcommon]
  · have hZ : 1≤729*Y := by linarith
    have hlong' : Real.sqrt (norm r)*T^2≤X/729 := by linarith
    have hdown : (729*Y)^(-(B+1))≤X/729 :=
      (cubicTheta_dilated_lower_scale hY hB).trans (div_le_div_of_nonneg_right hYX (by norm_num))
    have hu := cubicTheta_dilated_upper_scale hY hB
    have hh := hlong r hr hsr (729*Y) (X/729) T hZ (by positivity) hT
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
