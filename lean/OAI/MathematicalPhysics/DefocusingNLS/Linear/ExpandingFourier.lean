import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeightProduct
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeightAddition
import OAI.MathematicalPhysics.DefocusingNLS.Linear.FourierAbsolute

namespace OAI

/-! # The exact Y_L Fourier realization and uniform ℓ¹ embedding -/

open scoped ENNReal ComplexConjugate

namespace DefocusingNLS

/-- Physical Fourier coefficients for a vector whose ℓ² norm is the exact `Y_L` norm. -/
noncomputable def expandingFourierCoefficient (a k L : ℝ) (f : FourierL2)
    (n : frequencyLattice) : ℂ :=
  ((expandingSobolevWeight a k L n)⁻¹ : ℝ) * f n

theorem weight_mul_expandingFourierCoefficient (a k L : ℝ) (hL : 1 ≤ L)
    (f : FourierL2) (n : frequencyLattice) :
    (expandingSobolevWeight a k L n : ℂ) * expandingFourierCoefficient a k L f n = f n := by
  unfold expandingFourierCoefficient
  rw [← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (expandingSobolevWeight_pos a k L hL n).ne']
  simp

/-- The Hilbert norm equals the manuscript's volume-weighted Fourier norm exactly. -/
theorem expandingFourier_norm_sq (a k L : ℝ) (hL : 1 ≤ L) (f : FourierL2) :
    (2 * Real.pi * L) ^ 12 * (∑' n : frequencyLattice,
      ((L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) + (‖n‖ / L) ^ (2 * k)) *
        ‖expandingFourierCoefficient a k L f n‖ ^ 2) = ‖f‖ ^ 2 := by
  rw [← tsum_mul_left]
  have hn := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
  rw [hn]
  apply tsum_congr
  intro n
  have he : (2 * Real.pi * L) ^ 12 *
      ((L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) + (‖n‖ / L) ^ (2 * k)) =
      (expandingSobolevWeight a k L n) ^ 2 := by
    rw [expandingSobolevWeight_sq a k L hL]
    exact expandingSobolevWeightSq_original a k L hL n
  rw [← mul_assoc, he, ← mul_pow]
  have hw : expandingSobolevWeight a k L n * ‖expandingFourierCoefficient a k L f n‖ =
      ‖f n‖ := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (expandingSobolevWeight_pos a k L hL n)] using
        congrArg norm (weight_mul_expandingFourierCoefficient a k L hL f n)
  rw [hw]

theorem expanding_observation_weight_sq (a k L : ℝ) (hL : 1 ≤ L) (n : frequencyLattice) :
    ‖(((expandingSobolevWeight a k L n)⁻¹ : ℝ) : ℂ)‖ ^ 2 =
      ((2 * Real.pi) ^ 12)⁻¹ * (expandingSobolevWeightSq a k L n)⁻¹ := by
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_pos (expandingSobolevWeight_pos a k L hL n), inv_pow,
    expandingSobolevWeight_sq a k L hL n, mul_inv_rev]
  ring

/-- Inverse weights form an ℓ² vector with a uniform norm as the torus expands. -/
noncomputable def expandingObservationVector (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) : FourierL2 :=
  ⟨fun n => ((expandingSobolevWeight a k L n)⁻¹ : ℝ), by
    apply memℓp_gen
    have hs := (summable_expandingSobolevWeight_inv a k L ha ha1 hk hL).1.mul_left
      (((2 * Real.pi) ^ 12)⁻¹)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      expanding_observation_weight_sq a k L hL] using hs⟩

noncomputable def expandingEmbeddingBound (a k : ℝ) : ℝ :=
  Real.sqrt (((2 * Real.pi) ^ 12)⁻¹ *
    (2 ^ 12 * (1 + 2 * (1 / (a / 6) + 1 / (k / 6 - 1))) ^ 12))

theorem expandingObservationVector_norm_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) :
    ‖expandingObservationVector a k L ha ha1 hk hL‖ ≤ expandingEmbeddingBound a k := by
  have he := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (expandingObservationVector a k L ha ha1 hk hL)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at he
  have he' : ‖expandingObservationVector a k L ha ha1 hk hL‖ ^ 2 =
      ((2 * Real.pi) ^ 12)⁻¹ * ∑' n : frequencyLattice,
        (expandingSobolevWeightSq a k L n)⁻¹ := by
    rw [he, ← tsum_mul_left]
    apply tsum_congr
    intro n
    exact expanding_observation_weight_sq a k L hL n
  have hb := mul_le_mul_of_nonneg_left
    (summable_expandingSobolevWeight_inv a k L ha ha1 hk hL).2
    (show 0 ≤ ((2 * Real.pi) ^ 12)⁻¹ by positivity)
  rw [← he'] at hb
  have hC : 0 ≤ ((2 * Real.pi) ^ 12)⁻¹ *
      (2 ^ 12 * (1 + 2 * (1 / (a / 6) + 1 / (k / 6 - 1))) ^ 12) := by positivity
  unfold expandingEmbeddingBound
  nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg (((2 * Real.pi) ^ 12)⁻¹ *
    (2 ^ 12 * (1 + 2 * (1 / (a / 6) + 1 / (k / 6 - 1))) ^ 12)),
    norm_nonneg (expandingObservationVector a k L ha ha1 hk hL)]

theorem hasSum_expandingFourierCoefficient (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    HasSum (expandingFourierCoefficient a k L f)
      (inner ℂ (expandingObservationVector a k L ha ha1 hk hL) f) := by
  change HasSum (fun n => expandingFourierCoefficient a k L f n) _
  have h := lp.hasSum_inner (𝕜 := ℂ) (expandingObservationVector a k L ha ha1 hk hL) f
  simpa [expandingObservationVector, expandingFourierCoefficient, RCLike.inner_apply', mul_comm] using h

theorem summable_norm_expandingFourierCoefficient (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    Summable (fun n => ‖expandingFourierCoefficient a k L f n‖) :=
  (hasSum_expandingFourierCoefficient a k L ha ha1 hk hL f).summable.norm

theorem expandingFourierCoefficient_absolute (a k L : ℝ) (hL : 1 ≤ L)
    (f : FourierL2) (n : frequencyLattice) :
    expandingFourierCoefficient a k L (fourierAbsolute f) n =
      (‖expandingFourierCoefficient a k L f n‖ : ℂ) := by
  simp only [expandingFourierCoefficient, fourierAbsolute_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_inv, abs_of_pos (expandingSobolevWeight_pos a k L hL n),
    Complex.ofReal_mul]

/-- The ℓ¹ Fourier embedding constant is independent of the expanding scale. -/
theorem tsum_norm_expandingFourierCoefficient_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    (∑' n, ‖expandingFourierCoefficient a k L f n‖) ≤ expandingEmbeddingBound a k * ‖f‖ := by
  have h := hasSum_expandingFourierCoefficient a k L ha ha1 hk hL (fourierAbsolute f)
  change HasSum (fun n => expandingFourierCoefficient a k L (fourierAbsolute f) n) _ at h
  simp_rw [expandingFourierCoefficient_absolute a k L hL] at h
  have hs := (summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f).hasSum.mapL
    Complex.ofRealCLM
  have hs' : HasSum (fun n => (‖expandingFourierCoefficient a k L f n‖ : ℂ))
      (Complex.ofReal (∑' n, ‖expandingFourierCoefficient a k L f n‖)) := by
    simpa only [Complex.ofRealCLM_apply] using hs
  have heq := h.unique hs'
  have hb := norm_inner_le_norm (𝕜 := ℂ)
    (expandingObservationVector a k L ha ha1 hk hL) (fourierAbsolute f)
  rw [heq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg (fun n => norm_nonneg _)), fourierAbsolute_norm] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (expandingObservationVector_norm_le a k L ha ha1 hk hL) (norm_nonneg f))

end DefocusingNLS

end OAI
