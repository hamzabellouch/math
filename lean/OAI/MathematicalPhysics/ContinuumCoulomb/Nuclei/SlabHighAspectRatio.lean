import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabResidualScale

namespace OAI

/-! A slab aspect ratio compatible with the nuclear cubature scale.
The 72nd value moment permits horizontal radius T^10 at height T. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabUniformBound_tenthPower {rho T : ℝ} (hrho : 0 ≤ rho) (hT : 1 ≤ T) :
    slabUniformBound rho (T^10) T ≤ slabGrowthConstant rho*T^21 := by
  rw [slabUniformBound, slabDomain_volume (by positivity) (by linarith)]
  have hp : 1 ≤ T^21 := one_le_pow₀ hT
  have h1 : rho*NeutralAtom.kernelBallMass 1 ≤ rho*|NeutralAtom.kernelBallMass 1| *T^21 := by
    calc
      _ ≤ rho*|NeutralAtom.kernelBallMass 1| := mul_le_mul_of_nonneg_left (le_abs_self _) hrho
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hrho (abs_nonneg _)) hp
  dsimp [slabGrowthConstant]
  nlinarith only [h1]

def slabResidualSeventySecondBound (rho freq : ℝ) (u : PlanarPosition) : ℝ :=
  72*Real.pi^2*rho^2+8192*rho^2*localizedDensityMoment freq u 4+
    8*(slabGrowthConstant rho)^2*localizedDensityMoment freq u 72+
    8*Real.pi^2*rho^2*localizedDensityMoment freq u 72

private theorem div_pow_le_div_fourteenth {T C : ℝ} (hT : 1 ≤ T) (hC : 0 ≤ C)
    {k : ℕ} (hk : 14 ≤ k) : C/T^k ≤ C/T^14 :=
  div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_right₀ hT hk)

theorem slabSeventySecondTail_tenthPower_bound {rho T freq : ℝ}
    (hrho : 0 ≤ rho) (hT : 2 ≤ T) (u : PlanarPosition) :
    2*(6*Real.pi*rho*T^3/T^10)^2+
      2*(64*rho*T/T^10)^2*localizedDensityMoment freq u 4+
      2*(2*slabUniformBound rho (T^10) T)^2*(localizedDensityMoment freq u 72/T^72)+
      2*(2*Real.pi*rho)^2*(localizedDensityMoment freq u 72/T^68) ≤
      slabResidualSeventySecondBound rho freq u/T^14 := by
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hB0 : 0 ≤ slabUniformBound rho (T^10) T := by
    have h0 := slabPotential_abs_bound hrho (pow_nonneg hTpos.le 10) hTpos.le (0 : Position)
    exact (abs_nonneg _).trans h0
  have hB := (sq_le_sq₀ hB0 (by dsimp [slabGrowthConstant]; positivity)).mpr
    (slabUniformBound_tenthPower hrho hT1)
  have hBterm : 2*(2*slabUniformBound rho (T^10) T)^2*
      (localizedDensityMoment freq u 72/T^72) ≤
      8*(slabGrowthConstant rho)^2*localizedDensityMoment freq u 72/T^30 := by
    have hb := mul_le_mul_of_nonneg_right hB
      (show 0 ≤ 8*(localizedDensityMoment freq u 72/T^72) by
        exact mul_nonneg (by norm_num) (div_nonneg (localizedDensityMoment_nonnegative _ _ _)
          (pow_nonneg hTpos.le _)))
    convert hb using 1
    all_goals field_simp [ne_of_gt hTpos]
    all_goals ring
  have he1 : 2*(6*Real.pi*rho*T^3/T^10)^2 = 72*Real.pi^2*rho^2/T^14 := by
    field_simp [ne_of_gt hTpos]
    ring
  have he2 : 2*(64*rho*T/T^10)^2*localizedDensityMoment freq u 4 =
      8192*rho^2*localizedDensityMoment freq u 4/T^18 := by
    field_simp [ne_of_gt hTpos]
    ring
  have he4 : 2*(2*Real.pi*rho)^2*(localizedDensityMoment freq u 72/T^68) =
      8*Real.pi^2*rho^2*localizedDensityMoment freq u 72/T^68 := by ring
  rw [he1,he2,he4]
  have h2 := div_pow_le_div_fourteenth hT1
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤8192) (sq_nonneg rho))
      (localizedDensityMoment_nonnegative freq u 4)) (by decide : 14 ≤ 18)
  have h3 := div_pow_le_div_fourteenth hT1
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤8) (sq_nonneg (slabGrowthConstant rho)))
      (localizedDensityMoment_nonnegative freq u 72)) (by decide : 14 ≤ 30)
  have h4 := div_pow_le_div_fourteenth hT1
    (mul_nonneg (by positivity : 0 ≤ 8*Real.pi^2*rho^2)
      (localizedDensityMoment_nonnegative freq u 72)) (by decide : 14 ≤ 68)
  have hs := add_le_add (add_le_add (add_le_add (le_refl (72*Real.pi^2*rho^2/T^14)) h2) (hBterm.trans h3)) h4
  simpa only [slabResidualSeventySecondBound, add_div] using hs

theorem slabOrbitalResidual_tenthPower_bound {rho T freq : ℝ}
    (hrho : 0 ≤ rho) (hT : 2 ≤ T) (hfreq : 0 < freq) (u : PlanarPosition) :
    (∫ x, slabOrbitalResidual rho (T^10) T freq u x^2) ≤
      slabResidualSeventySecondBound rho freq u/T^14 := by
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hT4 : T ≤ T^10/2 := by
    have h2 : 2*T ≤ T^2 := by nlinarith [mul_nonneg hTpos.le (sub_nonneg.mpr hT)]
    have h4 : T^2 ≤ T^10 := pow_le_pow_right₀ hT1 (by decide : 2 ≤ 10)
    linarith
  exact (slabOrbitalResidual_square_bound_seventySecond hrho (pow_pos hTpos 10)
    hTpos.le hfreq hTpos hT4 le_rfl u).trans
      (slabSeventySecondTail_tenthPower_bound hrho hT u)

end ContinuumCoulomb

end

end OAI
