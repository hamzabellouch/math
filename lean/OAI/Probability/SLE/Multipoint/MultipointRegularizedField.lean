import OAI.Probability.SLE.Multipoint.MultipointLogAngular

namespace OAI

/-! The actual smooth factor on either side of a regulator midpoint.
Its only parameters are the constant and logarithmic slope of that branch. -/

noncomputable section

namespace SLEExactGauge.Multipoint

def regularizedLogFactor (κ D σ : ℝ) (z : ℂ × ℝ) (x : ℝ) : ℝ :=
  logFactor κ (greenExponent κ/2) (greenExponent κ) z x +
    D*(logFactor κ (greenExponent κ/2+σ) 0 z x +
      logFactor κ (greenExponent κ/2+σ) (q (greenExponent κ)) z x)

def branchRegulator (κ D σ : ℝ) (z : ℂ × ℝ) : ℝ :=
  D*Real.exp ((σ*κ/4)*(z.2-z.1.im))

lemma regularizedLogFactor_contDiff (κ D σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : (ℂ × ℝ) × ℝ => regularizedLogFactor κ D σ z.1 z.2) :=
  (logFactor_contDiff κ _ _).add (contDiff_const.mul
    ((logFactor_contDiff κ _ _).add (logFactor_contDiff κ _ _)))

lemma regularizedLogFactor_eq (κ D σ : ℝ) (z : ℂ × ℝ) (x : ℝ) :
    regularizedLogFactor κ D σ z x =
      Real.exp (((greenExponent κ/2)*κ/4)*(z.2-z.1.im))*
        angularFactor (greenExponent κ) (branchRegulator κ D σ z) (logAngle κ z x) := by
  unfold regularizedLogFactor
  rw [logFactor_eq_angular, logFactor_eq_angular, logFactor_eq_angular]
  have he : Real.exp (((greenExponent κ/2+σ)*κ/4)*(z.2-z.1.im)) =
      Real.exp (((greenExponent κ/2)*κ/4)*(z.2-z.1.im))*
        Real.exp ((σ*κ/4)*(z.2-z.1.im)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  simp only [sinePower, Real.rpow_zero, angularFactor, branchRegulator]
  ring

lemma regularizedLogFactor_pos (κ D σ : ℝ) (hD : 0 < D) (z : ℂ × ℝ) (x : ℝ) :
    0 < regularizedLogFactor κ D σ z x := by
  rw [regularizedLogFactor_eq]
  exact mul_pos (Real.exp_pos _) (angularFactor_pos (mul_pos hD (Real.exp_pos _))
    (logAngle_sin_pos κ z x))

lemma regularizedLogFactor_spatial (κ D σ : ℝ) (z : ℂ × ℝ) (x : ℝ) :
    deriv (regularizedLogFactor κ D σ z) x =
      Real.sqrt κ*logVelocity κ z x*
        Real.exp (((greenExponent κ/2)*κ/4)*(z.2-z.1.im))*
          angularFactorFirst (greenExponent κ) (branchRegulator κ D σ z) (logAngle κ z x) := by
  have hd := (logFactor_spatial_derivative κ (greenExponent κ/2) (greenExponent κ) z x).add
    (((logFactor_spatial_derivative κ (greenExponent κ/2+σ) 0 z x).add
      (logFactor_spatial_derivative κ (greenExponent κ/2+σ) (q (greenExponent κ)) z x)).const_mul D)
  change HasDerivAt (regularizedLogFactor κ D σ z) _ x at hd
  rw [hd.deriv]
  have hs (c r : ℝ) := logFactor_spatial_eq_angular κ c r z x
  rw [← (logFactor_spatial_derivative κ (greenExponent κ/2) (greenExponent κ) z x).deriv,
    ← (logFactor_spatial_derivative κ (greenExponent κ/2+σ) 0 z x).deriv,
    ← (logFactor_spatial_derivative κ (greenExponent κ/2+σ) (q (greenExponent κ)) z x).deriv]
  rw [hs, hs, hs]
  have he : Real.exp (((greenExponent κ/2+σ)*κ/4)*(z.2-z.1.im)) =
      Real.exp (((greenExponent κ/2)*κ/4)*(z.2-z.1.im))*
        Real.exp ((σ*κ/4)*(z.2-z.1.im)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  simp only [sinePowerFirst, zero_mul, angularFactorFirst, branchRegulator]
  ring

def logGenerator (κ : ℝ) (F : (ℂ × ℝ) → ℝ → ℝ) (z : ℂ × ℝ) (x : ℝ) : ℝ :=
  (fderiv ℝ (fun z => F z x) z) (physicalLogLoewnerField (Real.sqrt κ*x) z) +
    (1/2 : ℝ)*iteratedDeriv 2 (F z) x

lemma logGenerator_add (κ : ℝ) (F G : (ℂ × ℝ) → ℝ → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun z : (ℂ × ℝ) × ℝ => F z.1 z.2))
    (hG : ContDiff ℝ (⊤ : ℕ∞) (fun z : (ℂ × ℝ) × ℝ => G z.1 z.2))
    (z : ℂ × ℝ) (x : ℝ) :
    logGenerator κ (fun z x => F z x+G z x) z x =
      logGenerator κ F z x+logGenerator κ G z x := by
  have hFs : ContDiff ℝ (⊤ : ℕ∞) (fun z => F z x) :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  have hGs : ContDiff ℝ (⊤ : ℕ∞) (fun z => G z x) :=
    hG.comp (contDiff_id.prodMk contDiff_const)
  have hFx : ContDiff ℝ (⊤ : ℕ∞) (F z) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hGx : ContDiff ℝ (⊤ : ℕ∞) (G z) :=
    hG.comp (contDiff_const.prodMk contDiff_id)
  unfold logGenerator
  rw [fderiv_fun_add ((hFs.differentiable (by simp)) z) ((hGs.differentiable (by simp)) z),
    iteratedDeriv_fun_add (hFx.of_le (by simp)).contDiffAt (hGx.of_le (by simp)).contDiffAt]
  simp only [add_apply]
  ring

lemma logGenerator_const_mul (κ D : ℝ) (F : (ℂ × ℝ) → ℝ → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun z : (ℂ × ℝ) × ℝ => F z.1 z.2))
    (z : ℂ × ℝ) (x : ℝ) :
    logGenerator κ (fun z x => D*F z x) z x = D*logGenerator κ F z x := by
  have hFs : ContDiff ℝ (⊤ : ℕ∞) (fun z => F z x) :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  have hFx : ContDiff ℝ (⊤ : ℕ∞) (F z) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  unfold logGenerator
  rw [fderiv_const_mul ((hFs.differentiable (by simp)) z),
    iteratedDeriv_const_mul D (hFx.of_le (by simp)).contDiffAt]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem regularizedLogFactor_generator (κ D σ : ℝ) (hκ : 0 < κ)
    (z : ℂ × ℝ) (x : ℝ) :
    logGenerator κ (regularizedLogFactor κ D σ) z x =
      κ*logVelocity κ z x^2*
        Real.exp (((greenExponent κ/2)*κ/4)*(z.2-z.1.im))*
        branchRegulator κ D σ z *
          (greenExponent κ/2 +
            (greenExponent κ-q (greenExponent κ))*(1+q (greenExponent κ))/2*
              sinePower (q (greenExponent κ)) (logAngle κ z x) -
            negativeDrift (greenExponent κ)*
              sinePower (q (greenExponent κ)-2) (logAngle κ z x) +
            σ*(1+sinePower (q (greenExponent κ)) (logAngle κ z x))) := by
  unfold regularizedLogFactor
  rw [logGenerator_add κ _ _ (logFactor_contDiff κ _ _)
    (contDiff_const.mul ((logFactor_contDiff κ _ _).add (logFactor_contDiff κ _ _))),
    logGenerator_const_mul κ D _ ((logFactor_contDiff κ _ _).add (logFactor_contDiff κ _ _)),
    logGenerator_add κ _ _ (logFactor_contDiff κ _ _) (logFactor_contDiff κ _ _)]
  simp only [logGenerator, logFactor_generator_eq_angular κ _ _ hκ]
  have he : Real.exp (((greenExponent κ/2+σ)*κ/4)*(z.2-z.1.im)) =
      Real.exp (((greenExponent κ/2)*κ/4)*(z.2-z.1.im))*
        Real.exp ((σ*κ/4)*(z.2-z.1.im)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  have h0 : sineGenerator (greenExponent κ) 0 (logAngle κ z x) = 0 := by
    simp [sineGenerator, sinePowerFirst, sinePowerSecond]
  rw [h0]
  have hreg := regularized_generator (p := greenExponent κ)
    (δ := branchRegulator κ D σ z) (σ := σ) (logAngle_sin_pos κ z x)
  simp only [sinePower, Real.rpow_zero, branchRegulator] at hreg ⊢
  unfold angularFactor sinePower at hreg
  linear_combination (κ*logVelocity κ z x^2*
    Real.exp (((greenExponent κ/2)*κ/4)*(z.2-z.1.im)))*hreg

end SLEExactGauge.Multipoint

end

end OAI
