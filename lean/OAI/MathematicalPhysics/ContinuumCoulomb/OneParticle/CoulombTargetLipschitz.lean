import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombTargetRange

namespace OAI

/-! A quantitative modulus for the actual calibrated hopping residual.
The Coulomb gap keeps the square root away from zero, so ordinary dyadic
bisection needs no lower derivative bound. -/

noncomputable section
namespace ContinuumCoulomb

private theorem sqrt_abs_sub_le_of_lower {c a b : ℝ} (hc : 0 < c)
    (ha : c ≤ a) (hb : c ≤ b) :
    |Real.sqrt a-Real.sqrt b| ≤ |a-b|/(2*Real.sqrt c) := by
  have hc' : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have ha' : 0 ≤ a := hc.le.trans ha
  have hb' : 0 ≤ b := hc.le.trans hb
  have hsa := Real.sqrt_le_sqrt ha
  have hsb := Real.sqrt_le_sqrt hb
  have he : (Real.sqrt a-Real.sqrt b)*(Real.sqrt a+Real.sqrt b) = a-b := by
    nlinarith [Real.sq_sqrt ha', Real.sq_sqrt hb']
  have hab : |Real.sqrt a-Real.sqrt b| *(Real.sqrt a+Real.sqrt b) = |a-b| := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), ← abs_mul, he]
  apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hc')).mpr
  nlinarith [mul_le_mul_of_nonneg_left (show 2*Real.sqrt c ≤ Real.sqrt a+Real.sqrt b by linarith)
    (abs_nonneg (Real.sqrt a-Real.sqrt b))]

theorem localizedCoulombProfile_abs_sub {freq : ℝ} (hfreq : 0 < freq) (d e : ℝ) :
    |localizedCoulombProfile freq d-localizedCoulombProfile freq e| ≤
      localizedCoulombLipschitzConstant freq*|d-e| := by
  have h := localizedCoulombProfileAt_norm_sub hfreq (d • planarAxis 0) (e • planarAxis 0)
  rw [← sub_smul, norm_smul, planarAxis_zero_norm, mul_one] at h
  simpa only [localizedCoulombProfile, Real.norm_eq_abs] using h

def coulombTargetLipschitzConstant (freq τ K : ℝ) : ℝ :=
  τ*Real.sqrt K*localizedCoulombLipschitzConstant freq/(2*Real.sqrt (localizedGramConstant freq))

theorem coulombTargetLipschitzConstant_nonnegative (freq K : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ coulombTargetLipschitzConstant freq τ K := by
  unfold coulombTargetLipschitzConstant
  exact div_nonneg
    (mul_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _))
      (localizedCoulombLipschitzConstant_nonnegative freq))
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

theorem coulombHoppingTarget_abs_sub {freq τ K : ℝ} (hfreq : 0 < freq)
    (hτ : 0 ≤ τ) (hK : 0 ≤ K) (d e : ℝ)
    (hd : localizedGramConstant freq ≤ localizedCoulombProfile freq 0-localizedCoulombProfile freq d)
    (he : localizedGramConstant freq ≤ localizedCoulombProfile freq 0-localizedCoulombProfile freq e) :
    |coulombHoppingTarget freq τ K d-coulombHoppingTarget freq τ K e| ≤
      coulombTargetLipschitzConstant freq τ K*|d-e| := by
  have hc := localizedGramConstant_positive hfreq
  have hs := sqrt_abs_sub_le_of_lower hc hd he
  rw [show (localizedCoulombProfile freq 0-localizedCoulombProfile freq d) -
      (localizedCoulombProfile freq 0-localizedCoulombProfile freq e) =
      localizedCoulombProfile freq e-localizedCoulombProfile freq d by ring,
    abs_sub_comm (localizedCoulombProfile freq e) (localizedCoulombProfile freq d)] at hs
  have hl := div_le_div_of_nonneg_right (localizedCoulombProfile_abs_sub hfreq d e)
    (show 0 ≤ 2*Real.sqrt (localizedGramConstant freq) by positivity)
  unfold coulombHoppingTarget
  rw [Real.sqrt_mul hK, Real.sqrt_mul hK]
  rw [show τ*(Real.sqrt K*Real.sqrt (localizedCoulombProfile freq 0-localizedCoulombProfile freq d)) -
      τ*(Real.sqrt K*Real.sqrt (localizedCoulombProfile freq 0-localizedCoulombProfile freq e)) =
      (τ*Real.sqrt K)*(Real.sqrt (localizedCoulombProfile freq 0-localizedCoulombProfile freq d) -
        Real.sqrt (localizedCoulombProfile freq 0-localizedCoulombProfile freq e)) by ring,
    abs_mul, abs_of_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _))]
  calc
    _ ≤ (τ*Real.sqrt K) *
        (localizedCoulombLipschitzConstant freq*|d-e|/(2*Real.sqrt (localizedGramConstant freq))) :=
      mul_le_mul_of_nonneg_left (hs.trans hl) (mul_nonneg hτ (Real.sqrt_nonneg _))
    _ = _ := by unfold coulombTargetLipschitzConstant; ring

theorem calibratedResidual_abs_sub {freq τ K scale : ℝ} (hfreq : 0 < freq)
    (hτ : 0 ≤ τ) (hK : 0 ≤ K) (hscale : 0 ≤ scale) (d e : ℝ)
    (hd : localizedGramConstant freq ≤ localizedCoulombProfile freq 0-localizedCoulombProfile freq d)
    (he : localizedGramConstant freq ≤ localizedCoulombProfile freq 0-localizedCoulombProfile freq e) :
    |(scale*planarHopping d-coulombHoppingTarget freq τ K d) -
      (scale*planarHopping e-coulombHoppingTarget freq τ K e)| ≤
      (scale*(planarHoppingLipschitzConstant : ℝ)+coulombTargetLipschitzConstant freq τ K)*|d-e| := by
  have hh : |scale*(planarHopping d-planarHopping e)| ≤
      scale*(planarHoppingLipschitzConstant : ℝ)*|d-e| := by
    rw [abs_mul, abs_of_nonneg hscale]
    have h := planarHopping_norm_sub d e
    simp only [Real.norm_eq_abs] at h
    exact (mul_le_mul_of_nonneg_left h hscale).trans_eq (by ring)
  have ht := coulombHoppingTarget_abs_sub hfreq hτ hK d e hd he
  calc
    _ = |scale*(planarHopping d-planarHopping e) -
        (coulombHoppingTarget freq τ K d-coulombHoppingTarget freq τ K e)| := by congr 1; ring
    _ ≤ |scale*(planarHopping d-planarHopping e)| +
        |coulombHoppingTarget freq τ K d-coulombHoppingTarget freq τ K e| := abs_sub _ _
    _ ≤ _ := (add_le_add hh ht).trans_eq (by ring)

end ContinuumCoulomb

end

end OAI
