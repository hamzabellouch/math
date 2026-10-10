import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzCompactContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSamplingContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffResidualSampling
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzDyadicCutoff

namespace OAI

/-! # Continuous cutoff-profile and residual paths

These are the actual sampled physical functions.  The fixed-support rescaling
makes their Schwartz and Hilbert continuity independent of any symbol bounds.
The symbol bounds remain responsible for the separate uniform norm estimates.
-/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Scale" => {L : ℝ // 1 ≤ L}

noncomputable def compactDilationFamily (κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ)) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (L : ℝ) : 𝓢(E, ℂ) :=
  compactSmoothFamily κ hκ (fun p => Q (p.1 • p.2))
    (hQ.comp (contDiff_fst.smul contDiff_snd)) L

@[simp] theorem compactDilationFamily_apply (κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ)) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (L : ℝ) (x : E) : compactDilationFamily κ hκ Q hQ L x = κ x * Q (L • x) := rfl

theorem continuous_compactDilationFamily (κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ)) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    Continuous (compactDilationFamily κ hκ Q hQ) := by
  unfold compactDilationFamily
  exact continuous_compactSmoothFamily κ hκ _ _

private theorem continuous_scale_rpow (b : ℝ) :
    Continuous (fun L : Scale => L.1 ^ b) :=
  continuous_subtype_val.rpow_const
    (fun L => Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one L.2)))

noncomputable def normalizedCompactProfile (a : ℝ) (κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ)) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (L : Scale) : 𝓢(E, ℂ) :=
  (L.1 ^ (2 * a) : ℝ) • compactDilationFamily κ hκ Q hQ L.1

@[simp] theorem normalizedCompactProfile_apply (a : ℝ) (κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ)) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (L : Scale) (x : E) :
    normalizedCompactProfile a κ hκ Q hQ L x =
      κ x * ((L.1 ^ (2 * a) : ℝ) * Q (L.1 • x)) := by
  simp only [normalizedCompactProfile, smul_apply, compactDilationFamily_apply,
    Complex.real_smul]
  ring

theorem continuous_normalizedCompactProfile (a : ℝ) (κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ)) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    Continuous (normalizedCompactProfile a κ hκ Q hQ) :=
  (continuous_scale_rpow (2 * a)).smul
    ((continuous_compactDilationFamily κ hκ Q hQ).comp continuous_subtype_val)

section Residual

variable (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
  (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
  (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)

include hχone hχzero in
private theorem family_gradient_compact (j : Fin 12) :
    HasCompactSupport (cutoffGradientCoefficient χ j : E → ℂ) :=
  hasCompactSupport_of_cutoff_annulus _ (cutoffGradientCoefficient_annulus χ hχone hχzero j)

include hχone hχzero in
private theorem family_laplacian_compact :
    HasCompactSupport (cutoffLaplacianCoefficient χ : E → ℂ) :=
  hasCompactSupport_of_cutoff_annulus _ (cutoffLaplacianCoefficient_annulus χ hχone hχzero)

include hχone hχzero in
private theorem family_power_compact (m : ℕ) :
    HasCompactSupport (cutoffPowerCoefficient χ hχ m : E → ℂ) :=
  hasCompactSupport_of_cutoff_annulus _ (cutoffPowerCoefficient_annulus χ hχ m hχone hχzero)

/-- The normalized three-term residual is a continuous Schwartz family. -/
theorem continuous_normalizedCutoffResidualSchwartz (a : ℝ) (m : ℕ)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    Continuous (fun L : Scale =>
      normalizedCutoffResidualSchwartz χ hχ hχone hχzero a L.1 m Q hQ) := by
  let Qj (j : Fin 12) : E → ℂ :=
    fun x => fderiv ℝ Q x ((EuclideanSpace.basisFun (Fin 12) ℝ) j)
  have hQj (j : Fin 12) : ContDiff ℝ ∞ (Qj j) :=
    (contDiff_infty_iff_fderiv.mp hQ).2.clm_apply contDiff_const
  have hN : ContDiff ℝ ∞ (fun x => oddPowerNonlinearity m (Q x)) :=
    ((contDiff_oddPowerNonlinearity m).of_le (by simp)).comp hQ
  let A (j : Fin 12) := compactDilationFamily (cutoffGradientCoefficient χ j)
    (family_gradient_compact χ hχone hχzero j) (Qj j) (hQj j)
  let B := compactDilationFamily (cutoffLaplacianCoefficient χ)
    (family_laplacian_compact χ hχone hχzero) Q hQ
  let C := compactDilationFamily (cutoffPowerCoefficient χ hχ m)
    (family_power_compact χ hχ hχone hχzero m)
    (fun x => oddPowerNonlinearity m (Q x)) hN
  have hcA (j : Fin 12) : Continuous (fun L : Scale =>
      (L.1 ^ (2 * a + 1) : ℝ) • A j L.1) :=
    (continuous_scale_rpow _).smul
      ((continuous_compactDilationFamily _ _ _ _).comp continuous_subtype_val)
  have hcB : Continuous (fun L : Scale => (L.1 ^ (2 * a) : ℝ) • B L.1) :=
    (continuous_scale_rpow _).smul
      ((continuous_compactDilationFamily _ _ _ _).comp continuous_subtype_val)
  have hcC : Continuous (fun L : Scale =>
      ((L.1 ^ (2 * a)) ^ (2 * m + 1) : ℝ) • C L.1) :=
    ((continuous_scale_rpow _).pow _).smul
      ((continuous_compactDilationFamily _ _ _ _).comp continuous_subtype_val)
  have he (L : Scale) : normalizedCutoffResidualSchwartz χ hχ hχone hχzero a L.1 m Q hQ =
      (2 : ℂ) • (∑ j, (L.1 ^ (2 * a + 1) : ℝ) • A j L.1) +
        (L.1 ^ (2 * a) : ℝ) • B L.1 +
        ((L.1 ^ (2 * a)) ^ (2 * m + 1) : ℝ) • C L.1 := by
    ext x
    rw [normalizedCutoffResidualSchwartz_apply χ hχ hχone hχzero a L.1 m
      (lt_of_lt_of_le zero_lt_one L.2) Q hQ]
    simp only [add_apply, smul_apply, sum_apply, A, B, C, compactDilationFamily_apply,
      cutoffGradientCoefficient_apply, cutoffLaplacianCoefficient_apply,
      cutoffPowerCoefficient_apply, Complex.real_smul, Qj, normalizedCutoffResidual,
      oddPowerNonlinearity_real_mul]
    congr 1
    · congr 1
      · congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      · ring
    · ring
  simp_rw [he]
  exact ((continuous_finsetSum _ (fun j _ => hcA j)).const_smul (2 : ℂ)).add hcB |>.add hcC

end Residual

/-- The actual cutoff-profile sample varies continuously with the physical radius. -/
theorem continuous_cutoffProfile_sample (a k : ℝ) (ha : 0 < a)
    (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ))
    (hχ : HasCompactSupport (χ : E → ℂ)) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    Continuous (fun L : Scale => schwartzTorusSample a k L.1 ha1 hk L.2
      (radianFourierKernel
        (cutoffProfileSchwartz L.1 (lt_of_lt_of_le zero_lt_one L.2) χ hχ Q hQ))) := by
  have he (L : Scale) :
      cutoffProfileSchwartz L.1 (lt_of_lt_of_le zero_lt_one L.2) χ hχ Q hQ =
      schwartzPhysicalDilation a L.1 (lt_of_lt_of_le zero_lt_one L.2)
        (normalizedCompactProfile a χ hχ Q hQ L) := by
    ext x
    rw [cutoffProfileSchwartz_apply, schwartzPhysicalDilation_apply,
      normalizedCompactProfile_apply, smul_smul,
      mul_inv_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one L.2)), one_smul]
    have hp : L.1 ^ (-2 * a) * L.1 ^ (2 * a) = 1 := by
      rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one L.2)]
      simp
    symm
    calc
      _ = (L.1 ^ (-2 * a) * L.1 ^ (2 * a) : ℝ) *
          (χ (L.1⁻¹ • x) * Q x) := by push_cast; ring
      _ = _ := by rw [hp]; simp
  simp_rw [he]
  exact continuous_dilatedPhysicalSampling a k ha ha1 hk id continuous_id
    (normalizedCompactProfile a χ hχ Q hQ)
    (continuous_normalizedCompactProfile a χ hχ Q hQ)

/-- The exact PDE residual is a continuous forcing path in the sampled Hilbert model. -/
theorem continuous_cutoffResidual_sample (a k : ℝ) (ha : 0 < a)
    (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℝ))
    (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (m : ℕ) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    Continuous (fun L : Scale => schwartzTorusSample a k L.1 ha1 hk L.2
      (radianFourierKernel (cutoffResidualSchwartz χ hχ hχone hχzero a L.1
        (lt_of_lt_of_le zero_lt_one L.2) m Q hQ))) := by
  have he (L : Scale) :
      schwartzTorusSample a k L.1 ha1 hk L.2
        (radianFourierKernel (cutoffResidualSchwartz χ hχ hχone hχzero a L.1
          (lt_of_lt_of_le zero_lt_one L.2) m Q hQ)) =
      ((L.1 ^ (-2 : ℝ) : ℝ) : ℂ) • schwartzTorusSample a k L.1 ha1 hk L.2
        (radianFourierKernel (schwartzPhysicalDilation a L.1
          (lt_of_lt_of_le zero_lt_one L.2)
          (normalizedCutoffResidualSchwartz χ hχ hχone hχzero a L.1 m Q hQ))) := by
    exact map_smul (physicalSchwartzTorusSamplingLinear a k L.1 ha1 hk L.2)
      ((L.1 ^ (-2 : ℝ) : ℝ) : ℂ) _
  simp_rw [he]
  exact (Complex.continuous_ofReal.comp (continuous_scale_rpow (-2))).smul
    (continuous_dilatedPhysicalSampling a k ha ha1 hk id continuous_id _
      (continuous_normalizedCutoffResidualSchwartz χ hχ hχone hχzero a m Q hQ))

end DefocusingNLS

end OAI
