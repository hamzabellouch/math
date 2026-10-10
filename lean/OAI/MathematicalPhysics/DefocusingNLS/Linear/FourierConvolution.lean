import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchrodingerGenerator

namespace OAI

/-!
# Young's inequality for the Fourier lattice

An absolutely summable coefficient sequence convolves boundedly with an ℓ²
sequence. The proof sums translated ℓ² vectors, so no external convolution
estimate is assumed.
-/

open Filter Topology
open scoped ENNReal

namespace DefocusingNLS

/-- A Fourier vector with its indices shifted by `m`. -/
noncomputable def fourierTranslateVector (m : frequencyLattice) (f : FourierL2) : FourierL2 :=
  ⟨fun n => f (n - m), by
    apply memℓp_gen
    exact (Equiv.subRight m).summable_iff.mpr
      ((lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩

@[simp] theorem fourierTranslateVector_apply (m : frequencyLattice) (f : FourierL2)
    (n : frequencyLattice) : fourierTranslateVector m f n = f (n - m) := rfl

theorem fourierTranslateVector_norm (m : frequencyLattice) (f : FourierL2) :
    ‖fourierTranslateVector m f‖ = ‖f‖ := by
  have h1 := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (fourierTranslateVector m f)
  have h2 := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, fourierTranslateVector_apply] at h1 h2
  have heq : ‖fourierTranslateVector m f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [h1, h2]
    exact (Equiv.subRight m).tsum_eq (fun n => ‖f n‖ ^ 2)
  nlinarith [norm_nonneg f, norm_nonneg (fourierTranslateVector m f)]

/-- Translation of Fourier indices is a complex-linear isometry. -/
noncomputable def fourierTranslation (m : frequencyLattice) : FourierL2 →ₗᵢ[ℂ] FourierL2 where
  toFun := fourierTranslateVector m
  map_add' f g := by ext n; rfl
  map_smul' c f := by ext n; rfl
  norm_map' := fourierTranslateVector_norm m

@[simp] theorem fourierTranslation_apply (m : frequencyLattice) (f : FourierL2)
    (n : frequencyLattice) : fourierTranslation m f n = f (n - m) := rfl

/-- Discrete convolution, formed as an ℓ²-valued absolutely convergent series. -/
noncomputable def fourierConvolution (a : frequencyLattice → ℂ) (f : FourierL2) : FourierL2 :=
  ∑' m, a m • fourierTranslation m f

theorem summable_fourierConvolution_terms (a : frequencyLattice → ℂ)
    (ha : Summable (fun m => ‖a m‖)) (f : FourierL2) :
    Summable (fun m => a m • fourierTranslation m f) := by
  apply Summable.of_norm
  simpa only [norm_smul, LinearIsometry.norm_map] using ha.mul_right ‖f‖

/-- The ℓ²-valued construction agrees with the usual coefficient convolution. -/
theorem fourierConvolution_apply (a : frequencyLattice → ℂ)
    (ha : Summable (fun m => ‖a m‖)) (f : FourierL2) (n : frequencyLattice) :
    fourierConvolution a f n = ∑' m, a m * f (n - m) := by
  have h := (summable_fourierConvolution_terms a ha f).hasSum.mapL
    (lp.evalCLM ℂ (fun _ : frequencyLattice => ℂ) 2 n)
  exact h.tsum_eq.symm

/-- Young's `ℓ¹ * ℓ² → ℓ²` inequality on the twelve-dimensional lattice. -/
theorem fourierConvolution_norm_le (a : frequencyLattice → ℂ)
    (ha : Summable (fun m => ‖a m‖)) (f : FourierL2) :
    ‖fourierConvolution a f‖ ≤ (∑' m, ‖a m‖) * ‖f‖ := by
  have hs : Summable (fun m => ‖a m • fourierTranslation m f‖) := by
    simpa only [norm_smul, LinearIsometry.norm_map] using ha.mul_right ‖f‖
  calc
    _ ≤ ∑' m, ‖a m • fourierTranslation m f‖ := norm_tsum_le_tsum_norm hs
    _ = (∑' m, ‖a m‖) * ‖f‖ := by
      simp only [norm_smul, LinearIsometry.norm_map, tsum_mul_right]

end DefocusingNLS

end OAI
