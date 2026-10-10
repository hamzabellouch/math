import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevEmbedding

namespace OAI

/-! # Absolute Fourier coefficients and the quantitative ℓ¹ embedding -/

open scoped ENNReal

namespace DefocusingNLS

/-- Replace each ℓ² coordinate by its nonnegative norm, embedded in ℂ. -/
noncomputable def fourierAbsolute (f : FourierL2) : FourierL2 :=
  ⟨fun n => (‖f n‖ : ℂ), (lp.memℓp f).mono' (by intro n; simp)⟩

@[simp] theorem fourierAbsolute_apply (f : FourierL2) (n : frequencyLattice) :
    fourierAbsolute f n = (‖f n‖ : ℂ) := rfl

@[simp] theorem fourierAbsolute_norm (f : FourierL2) : ‖fourierAbsolute f‖ = ‖f‖ := by
  apply le_antisymm
  · exact lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by intro n; simp)
  · exact lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by intro n; simp)

lemma sobolevFourierCoefficient_absolute (k : ℝ) (f : FourierL2) (n : frequencyLattice) :
    sobolevFourierCoefficient k (fourierAbsolute f) n =
      (‖sobolevFourierCoefficient k f n‖ : ℂ) := by
  unfold sobolevFourierCoefficient
  change (((1 + ‖n‖ ^ 2) ^ (-k / 2) : ℝ) : ℂ) * (‖f n‖ : ℂ) =
    (‖(((1 + ‖n‖ ^ 2) ^ (-k / 2) : ℝ) : ℂ) * f n‖ : ℂ)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _), Complex.ofReal_mul]

/-- The Sobolev-to-ℓ¹ estimate has the same constant as point evaluation. -/
theorem tsum_norm_sobolevFourierCoefficient_le (k : ℝ) (hk : 6 < k) (f : FourierL2) :
    (∑' n, ‖sobolevFourierCoefficient k f n‖) ≤
      ‖sobolevObservationVector k hk‖ * ‖f‖ := by
  have h := hasSum_sobolevFourierCoefficient k hk (fourierAbsolute f)
  change HasSum (fun n => sobolevFourierCoefficient k (fourierAbsolute f) n) _ at h
  simp_rw [sobolevFourierCoefficient_absolute] at h
  have hr := (summable_norm_sobolevFourierCoefficient k hk f).hasSum.mapL Complex.ofRealCLM
  have hr' : HasSum (fun n => (‖sobolevFourierCoefficient k f n‖ : ℂ))
      (Complex.ofReal (∑' n, ‖sobolevFourierCoefficient k f n‖)) := by
    simpa only [Complex.ofRealCLM_apply] using hr
  have heq : sobolevCenterEvaluation k hk (fourierAbsolute f) =
      Complex.ofReal (∑' n, ‖sobolevFourierCoefficient k f n‖) := h.unique hr'
  have hb := sobolevCenterEvaluation_bound k hk (fourierAbsolute f)
  rw [heq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg (fun n => norm_nonneg _)), fourierAbsolute_norm] at hb
  exact hb

end DefocusingNLS

end OAI
