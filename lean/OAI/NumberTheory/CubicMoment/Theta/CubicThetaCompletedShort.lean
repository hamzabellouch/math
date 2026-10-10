import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCompletedShort

namespace OAI

/-! The finite primal estimate covers the fixed transition range in the
actual theta normalization by an exact dilation of its smooth weight. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaDilatedWeight (W : ℝ→ℂ) (x : ℝ) : ℂ := W (x/729)

lemma cubicThetaDilatedWeight_compact {W : ℝ→ℂ} (hW : HasCompactSupport W) :
    HasCompactSupport (cubicThetaDilatedWeight W) := by
  change HasCompactSupport (fun x => W (x/729))
  simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm,one_mul] using
    hW.comp_smul (by norm_num : (1/729:ℝ)≠0)

lemma cubicThetaDilatedWeight_continuous {W : ℝ→ℂ} (hW : Continuous W) :
    Continuous (cubicThetaDilatedWeight W) := hW.comp (by fun_prop)

lemma cubicThetaHeight_dilated (r : Eisenstein) (ℓ : ℤ) (W : ℝ→ℂ) (X t : ℝ) :
    metaplecticHeightCompleted r ℓ (cubicThetaDilatedWeight W) (X/729) t=
      metaplecticHeightCompleted r ℓ W X t := by
  unfold metaplecticHeightCompleted
  apply tsum_congr
  intro du
  have he (v : ℝ) : (v/(X/729))/729=v/X := by ring
  simp only [metaplecticPrimalCoefficient,cubicThetaDilatedWeight,he]

theorem cubicTheta_completed_short_mean
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0≤C)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hc : Continuous W)
    {η B : ℝ} (hη : 0<η) (hB : 0≤B) :
    ∃ K : ℝ, 0≤K ∧ ∀ r : Eisenstein, primary r →
      ∀ (ℓ : ℤ) (Y X T u : ℝ), 1≤Y → 0<X → 1≤T → X≤Y^B →
      X≤729*Real.sqrt (norm r)*T^2 →
      (∫ t in T..2*T,‖metaplecticHeightCompleted r ℓ W X (t+u)‖)/T≤
        K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  obtain ⟨K,hK,hbound⟩ := metaplectic_completed_short_mean hMV hC
    (cubicThetaDilatedWeight W) (cubicThetaDilatedWeight_compact hW)
    (cubicThetaDilatedWeight_continuous hc) hη hB
  refine ⟨K,hK,?_⟩
  intro r hr ℓ Y X T u hY hX hT hXY hshort
  have hscale : X/729≤X := by linarith
  have hs : X/729≤Real.sqrt (norm r)*T^2 := by linarith
  have hb := hbound r hr ℓ Y (X/729) T u hY (by positivity) hT (hscale.trans hXY) hs
  simp only [cubicThetaHeight_dilated] at hb
  apply hb.trans
  have hn := norm_nonneg r
  gcongr

end CubicFirstMoment

end

end OAI
