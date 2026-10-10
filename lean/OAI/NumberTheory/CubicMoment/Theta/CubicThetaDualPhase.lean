import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDualFrequency

namespace OAI

/-! The exact angular phase of the constructed dual formula. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_theta_lambda (ℓ : ℤ) : theta ℓ lambdaE=Complex.I^ℓ := by
  have hnorm : ‖traceLambda‖=Real.sqrt 3 := by
    rw [traceLambda_eq,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  unfold theta
  rw [lambdaE_coe,hnorm,traceLambda_eq]
  congr 1
  exact mul_div_cancel_left₀ Complex.I (Complex.ofReal_ne_zero.mpr (by positivity))

lemma cubicTheta_root_ratio {r : Eisenstein} (hr : primary r) (rev : Bool) (k : ℕ) :
    cubicThetaLevelAngularRoot r rev k=
      (-(star (r:ℂ)/(r:ℂ)))^(cubicThetaCircleOrder (!rev) k) := by
  have hz : (r:ℂ)≠0 := fun h => primary_ne_zero hr (Subtype.ext h)
  have hn : (norm r:ℂ)=(r:ℂ)*star (r:ℂ) := by
    simpa only [norm,Complex.star_def,Complex.normSq_eq_norm_sq,Complex.ofReal_pow] using (Complex.mul_conj' (r:ℂ)).symm
  have he : -(norm r:ℂ)/(r:ℂ)^2=-(star (r:ℂ)/(r:ℂ)) := by
    rw [hn]
    field_simp
  rw [cubicThetaLevelAngularRoot,he]
  cases rev
  · simp only [Bool.not_false,cubicThetaCircleMultiplier,ite_true,cubicThetaCircleOrder,
      star_neg,zpow_neg,zpow_natCast]
    rw [←inv_pow,inv_neg,inv_div]
    simp only [Complex.star_def,map_div₀,starRingEnd_self_apply]
  · simp only [Bool.not_true,cubicThetaCircleMultiplier,Bool.false_eq_true,ite_false,
      cubicThetaCircleOrder,zpow_natCast]

lemma cubicTheta_root_phase {r : Eisenstein} (hr : primary r) (rev : Bool) (k : ℕ) :
    (cubicThetaLevelAngularRoot r rev k)⁻¹*
      theta (cubicThetaCircleOrder rev k) lambdaE=
    theta (cubicThetaCircleOrder (!rev) k) lambdaE*
      (star (r:ℂ)/(r:ℂ))^(-cubicThetaCircleOrder (!rev) k) := by
  let ℓ := cubicThetaCircleOrder (!rev) k
  let q := star (r:ℂ)/(r:ℂ)
  have hq : q≠0 := div_ne_zero (star_ne_zero.mpr (by
    intro h
    exact primary_ne_zero hr (Subtype.ext h))) (by
      intro h
      exact primary_ne_zero hr (Subtype.ext h))
  have hI : -q*Complex.I=Complex.I⁻¹*q := by rw [Complex.inv_I]; ring
  have he : (-q)^ℓ*Complex.I^ℓ=Complex.I^(-ℓ)*q^ℓ := by
    rw [←mul_zpow,hI,mul_zpow,inv_zpow,←zpow_neg]
  rw [cubicTheta_root_ratio hr,cubicThetaCircleOrder_neg rev k,
    cubicTheta_theta_lambda,cubicTheta_theta_lambda]
  change ((-q)^ℓ)⁻¹*Complex.I^(-ℓ)=Complex.I^ℓ*q^(-ℓ)
  apply mul_right_cancel₀ (zpow_ne_zero ℓ hq)
  calc
    _ = ((-q)^ℓ)⁻¹*(Complex.I^(-ℓ)*q^ℓ) := by ring
    _ = ((-q)^ℓ)⁻¹*((-q)^ℓ*Complex.I^ℓ) := by rw [he]
    _ = Complex.I^ℓ := by
      rw [←mul_assoc,inv_mul_cancel₀ (zpow_ne_zero _ (neg_ne_zero.mpr hq)),one_mul]
    _ = _ := by rw [mul_assoc,zpow_neg,inv_mul_cancel₀ (zpow_ne_zero _ hq),mul_one]

end CubicFirstMoment

end

end OAI
