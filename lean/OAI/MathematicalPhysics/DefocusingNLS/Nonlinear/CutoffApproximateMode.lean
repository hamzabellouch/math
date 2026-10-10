import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffFourierDefect

namespace OAI

/-! # The actual sampled cutoff profile satisfies the forced mode equation

The smooth stationary-profile premise is explicit. The forcing is the already
constructed three-term cutoff residual, with the same physical normalization.
-/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem cutoffProfileSchwartz_dilation_zero (R : ℝ) (hR : 0 < R)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    cutoffProfileSchwartz R hR χ hχ Q hQ =
      schwartzPhysicalDilation 0 R hR (compactDilationFamily χ hχ Q hQ R) := by
  ext x
  simp only [cutoffProfileSchwartz_apply, schwartzPhysicalDilation_apply,
    compactDilationFamily_apply, mul_zero, Real.rpow_zero, Complex.ofReal_one,
    one_mul, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]

theorem schwartzOddPower_dilation_zero (R : ℝ) (hR : 0 < R)
    (ψ : 𝓢(E, ℂ)) (m : ℕ) :
    schwartzOddPower m (schwartzPhysicalDilation 0 R hR ψ) =
      schwartzPhysicalDilation 0 R hR (schwartzOddPower m ψ) := by
  ext x
  simp only [schwartzOddPower_apply, schwartzPhysicalDilation_apply, mul_zero,
    Real.rpow_zero, Complex.ofReal_one, one_mul]

theorem cutoffProfileSchwartz_zero_outside (R : ℝ) (hR : 0 < R)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (x : E) (hx : 2 * R < ‖x‖) :
    cutoffProfileSchwartz R hR (χ.postcompCLM Complex.ofRealCLM)
      (hasCompactSupport_complexCutoff χ hχ) Q hQ x = 0 := by
  have hr : 2 < ‖R⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    exact (lt_inv_mul_iff₀' hR).mpr hx
  simp only [cutoffProfileSchwartz_apply, SchwartzMap.postcompCLM_apply,
    Complex.ofRealCLM_apply, hχzero _ hr, Complex.ofReal_zero, zero_mul]

theorem cutoff_normalized_nonlinearity_coefficient (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hR : 1 ≤ R) (m : ℕ)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (n : frequencyLattice) :
    physicalSchwartzCoefficient 1 n (schwartzOddPower m
      (compactDilationFamily (χ.postcompCLM Complex.ofRealCLM)
        (hasCompactSupport_complexCutoff χ hχ) Q hQ R)) =
    expandingFourierCoefficient a k R
      (expandingOddPower a k R ha ha1 hk hR m
        (schwartzTorusSample a k R ha1 hk hR (radianFourierKernel
          (cutoffProfileSchwartz R (lt_of_lt_of_le zero_lt_one hR)
            (χ.postcompCLM Complex.ofRealCLM)
            (hasCompactSupport_complexCutoff χ hχ) Q hQ)))) n := by
  rw [sampled_oddPower_coefficient a k R ha ha1 hk hR m _
    (cutoffProfileSchwartz_zero_outside R (lt_of_lt_of_le zero_lt_one hR)
      χ hχ hχzero Q hQ)]
  change _ = physicalSchwartzCoefficient R n _
  rw [cutoffProfileSchwartz_dilation_zero, schwartzOddPower_dilation_zero,
    physicalSchwartzCoefficient_dilation]

theorem cutoff_normalized_defect_coefficient (a b R : ℝ) (hR : 0 < R)
    (m : ℕ) (ham : 2 * a * (m : ℝ) = 1)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hstationary : ∀ y, stationarySimilarityDefect a b m Q y = 0) (n : frequencyLattice) :
    physicalSchwartzCoefficient 1 n (normalizedCutoffDefectSchwartz a b R m
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ) =
      physicalSchwartzCoefficient R n
        (cutoffResidualSchwartz χ hχ hχone hχzero a R hR m Q hQ) := by
  have he : schwartzPhysicalDilation 0 R hR
      (normalizedCutoffDefectSchwartz a b R m
        (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ) =
      cutoffResidualSchwartz χ hχ hχone hχzero a R hR m Q hQ := by
    ext y
    rw [schwartzPhysicalDilation_apply,
      normalizedCutoffDefectSchwartz_apply a b R hR m χ hχ Q hQ,
      hstationary,
      cutoffResidualSchwartz_apply χ hχ hχone hχzero a R hR m ham Q hQ]
    simp only [mul_zero, zero_add, Real.rpow_zero, Complex.ofReal_one, one_mul,
      smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  rw [← he, physicalSchwartzCoefficient_dilation]

noncomputable def cutoffSampledMode (L : ℝ) (χ : 𝓢(E, ℂ))
    (hχ : HasCompactSupport (χ : E → ℂ)) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (n : frequencyLattice) (t : ℝ) : ℂ :=
  physicalSchwartzCoefficient 1 n (compactDilationFamily χ hχ Q hQ (expandingRadius L t))

theorem cutoffSampledMode_eq_physical (L : ℝ) (hL : 0 < L)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (n : frequencyLattice) (t : ℝ) :
    cutoffSampledMode L χ hχ Q hQ n t =
      physicalSchwartzCoefficient (expandingRadius L t) n
        (cutoffProfileSchwartz (expandingRadius L t)
          (mul_pos hL (Real.exp_pos _)) χ hχ Q hQ) := by
  exact (cutoffProfile_coefficient_fixed_scale _ (mul_pos hL (Real.exp_pos _))
    χ hχ Q hQ n).symm

theorem hasDerivAt_cutoffSampledMode (L s : ℝ) (hL : 0 < L)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (n : frequencyLattice) :
    HasDerivAt (cutoffSampledMode L χ hχ Q hQ n)
      (physicalSchwartzCoefficient 1 n (cutoffVelocitySchwartz χ hχ Q hQ (expandingRadius L s))) s := by
  have hd := hasDerivAt_cutoffProfile_coefficient L s hL χ hχ Q hQ n
  have he : (fun t => schwartzLatticeCoefficient (expandingRadius L t)
      (radianFourierKernel (cutoffProfileSchwartz (expandingRadius L t)
        (mul_pos hL (Real.exp_pos _)) χ hχ Q hQ)) n) =
      cutoffSampledMode L χ hχ Q hQ n := by
    funext t
    exact (cutoffSampledMode_eq_physical L hL χ hχ Q hQ n t).symm
  rw [he] at hd
  convert hd using 1
  simp only [physicalSchwartzCoefficient_apply, schwartzLatticeCoefficient,
    mul_one, inv_one, one_smul, radianFourierKernel_apply]
  rfl

/-- The sampled profile has the actual Fourier mode derivative, including the
same sampled residual used in the decaying Duhamel estimate. -/
theorem hasDerivAt_cutoffSampledMode_equation (a b k L s : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 0 < L)
    (hRs : 1 ≤ expandingRadius L s) (m : ℕ) (ham : 2 * a * (m : ℝ) = 1)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hstationary : ∀ y, stationarySimilarityDefect a b m Q y = 0) (n : frequencyLattice) :
    let R := expandingRadius L s
    let ψ := cutoffProfileSchwartz R (lt_of_lt_of_le zero_lt_one hRs)
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ
    let U := schwartzTorusSample a k R ha1 hk hRs (radianFourierKernel ψ)
    let residual := cutoffResidualSchwartz χ hχ hχone hχzero a R
      (lt_of_lt_of_le zero_lt_one hRs) m Q hQ
    HasDerivAt
      (cutoffSampledMode L (χ.postcompCLM Complex.ofRealCLM)
        (hasCompactSupport_complexCutoff χ hχ) Q hQ n)
      (((-(a : ℂ)) + Complex.I * ((b : ℂ) -
          (((R ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * ((‖n‖ ^ 2 : ℝ) : ℂ))) *
        cutoffSampledMode L (χ.postcompCLM Complex.ofRealCLM)
          (hasCompactSupport_complexCutoff χ hχ) Q hQ n s -
        Complex.I * expandingFourierCoefficient a k R
          (expandingOddPower a k R ha ha1 hk hRs m U) n -
        Complex.I * physicalSchwartzCoefficient R n residual) s := by
  intro R ψ U residual
  have hd := hasDerivAt_cutoffSampledMode L s hL
    (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ n
  have he := physicalSchwartzCoefficient_cutoffDefect a b R m
    (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ n
  rw [cutoff_normalized_defect_coefficient a b R
    (lt_of_lt_of_le zero_lt_one hRs) m ham χ hχ hχone hχzero Q hQ hstationary n,
    cutoff_normalized_nonlinearity_coefficient a k R ha ha1 hk hRs m
      χ hχ hχzero Q hQ n] at he
  apply hd.congr_deriv
  change physicalSchwartzCoefficient 1 n
    (cutoffVelocitySchwartz (χ.postcompCLM Complex.ofRealCLM)
      (hasCompactSupport_complexCutoff χ hχ) Q hQ R) = _
  change physicalSchwartzCoefficient R n residual =
    Complex.I * physicalSchwartzCoefficient 1 n
      (cutoffVelocitySchwartz (χ.postcompCLM Complex.ofRealCLM)
        (hasCompactSupport_complexCutoff χ hχ) Q hQ R) +
    (-(((R ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * ((‖n‖ ^ 2 : ℝ) : ℂ) +
      Complex.I * (a : ℂ) + (b : ℂ)) *
        cutoffSampledMode L (χ.postcompCLM Complex.ofRealCLM)
          (hasCompactSupport_complexCutoff χ hχ) Q hQ n s -
    expandingFourierCoefficient a k R (expandingOddPower a k R ha ha1 hk hRs m U) n at he
  linear_combination Complex.I * he +
    (physicalSchwartzCoefficient 1 n
      (cutoffVelocitySchwartz (χ.postcompCLM Complex.ofRealCLM)
        (hasCompactSupport_complexCutoff χ hχ) Q hQ R) +
      (a : ℂ) * cutoffSampledMode L (χ.postcompCLM Complex.ofRealCLM)
        (hasCompactSupport_complexCutoff χ hχ) Q hQ n s) * Complex.I_sq

end DefocusingNLS

end OAI
