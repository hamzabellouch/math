import OAI.Probability.SLE.Angle.AngleLogCosineDerivatives

namespace OAI

/-! The exact drift and variance coefficients after the Green change of
law, in the paper's logarithmic conformal-radius clock. -/
noncomputable section

namespace SLEExactGauge

lemma shifted_green_generator {κ : ℝ} (hκ : 0<κ) (c : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    (fderiv ℝ (fun r : ℂ × ℝ => powerLogDensity κ (codimension κ+c) (greenExponent κ) r x) q)
        (physicalLogLoewnerField (Real.sqrt κ*x) q)+
      (1/2:ℝ)*iteratedDeriv 2 (powerLogDensity κ (codimension κ+c) (greenExponent κ) q) x =
    powerLogDensity κ (codimension κ+c) (greenExponent κ) q x*logClockRate κ q x*c := by
  rw [power_physical_generator κ _ _ hκ.le]
  unfold logClockRate greenExponent codimension dimension
  have h0 := hκ.ne'
  field_simp
  ring

lemma logCosine_tilted_drift {κ : ℝ} (hκ : 0<κ) (q : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun r : ℂ × ℝ => logCosine κ r x) q
        (physicalLogLoewnerField (Real.sqrt κ*x) q)+
      (1/2:ℝ)*iteratedDeriv 2 (logCosine κ q) x+
      (greenExponent κ*Real.sqrt κ*(q.1.re-Real.sqrt κ*x)/greenLogNormSq κ q x)*
        deriv (logCosine κ q) x =
    logClockRate κ q x*(-(1+κ/8)*logCosine κ q x) := by
  rw [logCosine_physical_direction,logCosine_spatial_second hκ.le,(logCosine_spatial κ q x).deriv]
  unfold logClockRate logCosine greenExponent
  have hN := (greenLogNormSq_pos κ q x).ne'
  have hk := hκ.ne'
  field_simp
  rw [Real.sq_sqrt hκ.le]
  ring

lemma logCosine_tilted_variance {κ : ℝ} (hκ : 0≤κ) (q : ℂ × ℝ) (x : ℝ) :
    (1/2:ℝ)*(deriv (logCosine κ q) x)^2=
      logClockRate κ q x*(κ/8)*(1-logCosine κ q x^2) := by
  rw [(logCosine_spatial κ q x).deriv]
  unfold logClockRate logCosine
  rw [div_pow,mul_pow,mul_pow,mul_pow,neg_sq,Real.sq_sqrt hκ,logInverseNorm_sq]
  have hN := (greenLogNormSq_pos κ q x).ne'
  field_simp
  unfold greenLogNormSq
  ring

end SLEExactGauge

end

end OAI
