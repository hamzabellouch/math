import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabOrbitalResidual

namespace OAI

/-! A polynomial choice of slab dimensions makes the actual orbital
residual small. The twenty-fourth moment absorbs the total slab mass. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabDomain_volume {H S : ℝ} (hH : 0 ≤ H) (hS : 0 ≤ S) :
    volume.real (slabDomain H S) = 8*H^2*S := by
  have h := (slabProduct_measurePreserving H S).measureReal_preimage
    (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  rw [Set.preimage_univ, measureReal_restrict_apply_univ] at h
  rw [← h, Measure.real, slabProductMeasure, Measure.pi_univ, Fin.prod_univ_three,
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [slabAxisMeasure, Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num [slabSide, ENNReal.toReal_ofReal, hH, hS]
  ring

def slabGrowthConstant (rho : ℝ) : ℝ :=
  rho*(|NeutralAtom.kernelBallMass 1|+8)

theorem slabUniformBound_polynomial {rho T : ℝ} (hrho : 0 ≤ rho) (hT : 1 ≤ T) :
    slabUniformBound rho (T^4) T ≤ slabGrowthConstant rho*T^9 := by
  rw [slabUniformBound, slabDomain_volume (by positivity) (by linarith)]
  have hp : 1 ≤ T^9 := one_le_pow₀ hT
  have h1 : rho*NeutralAtom.kernelBallMass 1 ≤ rho*|NeutralAtom.kernelBallMass 1| *T^9 := by
    calc
      _ ≤ rho*|NeutralAtom.kernelBallMass 1| := mul_le_mul_of_nonneg_left (le_abs_self _) hrho
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hrho (abs_nonneg _)) hp
  dsimp [slabGrowthConstant]
  nlinarith only [h1]

def slabResidualPolynomialBound (rho freq : ℝ) (u : PlanarPosition) : ℝ :=
  72*Real.pi^2*rho^2+8192*rho^2*localizedDensityMoment freq u 4+
    8*(slabGrowthConstant rho)^2*localizedDensityMoment freq u 24+
    8*Real.pi^2*rho^2*localizedDensityMoment freq u 24

private theorem div_pow_le_div_sq {T C : ℝ} (hT : 1 ≤ T) (hC : 0 ≤ C)
    {k : ℕ} (hk : 2 ≤ k) : C/T^k ≤ C/T^2 :=
  div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_right₀ hT hk)

theorem slabOrbitalResidual_polynomial_bound {rho T freq : ℝ}
    (hrho : 0 ≤ rho) (hT : 2 ≤ T) (hfreq : 0 < freq) (u : PlanarPosition) :
    (∫ x, slabOrbitalResidual rho (T^4) T freq u x^2) ≤
      slabResidualPolynomialBound rho freq u/T^2 := by
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hT4 : T ≤ T^4/2 := by
    have h2 : 2*T ≤ T^2 := by nlinarith [mul_nonneg hTpos.le (sub_nonneg.mpr hT)]
    have h4 : T^2 ≤ T^4 := by
      exact pow_le_pow_right₀ hT1 (by decide : 2 ≤ 4)
    linarith
  have h := slabOrbitalResidual_square_bound hrho (pow_pos hTpos 4) hTpos.le hfreq
    hTpos hT4 le_rfl u
  have hB0 : 0 ≤ slabUniformBound rho (T^4) T := by
    have h0 := slabPotential_abs_bound hrho (pow_nonneg hTpos.le 4) hTpos.le (0 : Position)
    exact (abs_nonneg _).trans h0
  have hB := (sq_le_sq₀ hB0 (by dsimp [slabGrowthConstant]; positivity)).mpr
    (slabUniformBound_polynomial hrho hT1)
  have hBterm : 2*(2*slabUniformBound rho (T^4) T)^2*
      (localizedDensityMoment freq u 24/T^24) ≤
      8*(slabGrowthConstant rho)^2*localizedDensityMoment freq u 24/T^6 := by
    have hb := mul_le_mul_of_nonneg_right hB
      (show 0 ≤ 8*(localizedDensityMoment freq u 24/T^24) by
        exact mul_nonneg (by norm_num) (div_nonneg (localizedDensityMoment_nonnegative _ _ _)
          (pow_nonneg hTpos.le _)))
    convert hb using 1
    all_goals field_simp [ne_of_gt hTpos]
    all_goals ring
  have he1 : 2*(6*Real.pi*rho*T^3/T^4)^2 = 72*Real.pi^2*rho^2/T^2 := by
    field_simp [ne_of_gt hTpos]
    ring
  have he2 : 2*(64*rho*T/T^4)^2*localizedDensityMoment freq u 4 =
      8192*rho^2*localizedDensityMoment freq u 4/T^6 := by
    field_simp [ne_of_gt hTpos]
    ring
  have he4 : 2*(2*Real.pi*rho)^2*(localizedDensityMoment freq u 24/T^20) =
      8*Real.pi^2*rho^2*localizedDensityMoment freq u 24/T^20 := by ring
  rw [he1,he2,he4] at h
  have h2 := div_pow_le_div_sq hT1
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤8192) (sq_nonneg rho))
      (localizedDensityMoment_nonnegative freq u 4)) (by decide : 2 ≤ 6)
  have h3 := div_pow_le_div_sq hT1
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤8) (sq_nonneg (slabGrowthConstant rho)))
      (localizedDensityMoment_nonnegative freq u 24)) (by decide : 2 ≤ 6)
  have h4 := div_pow_le_div_sq hT1
    (mul_nonneg (by positivity : 0 ≤ 8*Real.pi^2*rho^2)
      (localizedDensityMoment_nonnegative freq u 24)) (by decide : 2 ≤ 20)
  have hs := h.trans (add_le_add (add_le_add (add_le_add le_rfl h2) (hBterm.trans h3)) h4)
  simpa only [slabResidualPolynomialBound, add_div] using hs

end ContinuumCoulomb

end

end OAI
