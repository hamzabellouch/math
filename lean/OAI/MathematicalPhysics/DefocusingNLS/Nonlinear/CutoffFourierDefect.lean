import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadianFourierDerivatives
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSampledNonlinearity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffNormalizedEquation
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffProfileModeDerivative

namespace OAI

/-! # The exact Fourier transform of the normalized cutoff defect -/

open scoped SchwartzMap Laplacian ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def physicalSchwartzCoefficient (L : ℝ) (n : frequencyLattice) :
    𝓢(E, ℂ) →ₗ[ℂ] ℂ where
  toFun ψ := schwartzLatticeCoefficient L (radianFourierKernel ψ) n
  map_add' ψ φ := by
    change (((2 * Real.pi * L) ^ 12)⁻¹ : ℝ) *
      (radianFourierCLM (ψ + φ)) (L⁻¹ • (n : E)) =
        (((2 * Real.pi * L) ^ 12)⁻¹ : ℝ) * (radianFourierCLM ψ) (L⁻¹ • (n : E)) +
        (((2 * Real.pi * L) ^ 12)⁻¹ : ℝ) * (radianFourierCLM φ) (L⁻¹ • (n : E))
    rw [map_add]
    simp only [add_apply, mul_add]
  map_smul' c ψ := by
    change (((2 * Real.pi * L) ^ 12)⁻¹ : ℝ) *
      (radianFourierCLM (c • ψ)) (L⁻¹ • (n : E)) =
        c * ((((2 * Real.pi * L) ^ 12)⁻¹ : ℝ) * (radianFourierCLM ψ) (L⁻¹ • (n : E)))
    rw [map_smul radianFourierCLM]
    simp only [smul_apply, smul_eq_mul]
    ring

@[simp] theorem physicalSchwartzCoefficient_apply (L : ℝ) (n : frequencyLattice)
    (ψ : 𝓢(E, ℂ)) :
    physicalSchwartzCoefficient L n ψ =
      schwartzLatticeCoefficient L (radianFourierKernel ψ) n := rfl

theorem physicalSchwartzCoefficient_laplacian (ψ : 𝓢(E, ℂ)) (n : frequencyLattice) :
    physicalSchwartzCoefficient 1 n (Δ ψ) =
      -((‖n‖ ^ 2 : ℝ) : ℂ) * physicalSchwartzCoefficient 1 n ψ := by
  change (((2 * Real.pi * 1) ^ 12)⁻¹ : ℝ) *
      radianFourierKernel (Δ ψ) (1⁻¹ • (n : E)) = _
  simp only [inv_one, one_smul, radianFourierKernel_laplacian,
    physicalSchwartzCoefficient_apply, schwartzLatticeCoefficient, Submodule.norm_coe]
  ring

theorem physicalSchwartzCoefficient_dilation (R : ℝ) (hR : 0 < R)
    (ψ : 𝓢(E, ℂ)) (n : frequencyLattice) :
    physicalSchwartzCoefficient R n (schwartzPhysicalDilation 0 R hR ψ) =
      physicalSchwartzCoefficient 1 n ψ := by
  simp only [physicalSchwartzCoefficient_apply]
  rw [radianFourierKernel_schwartzPhysicalDilation,
    schwartzLatticeCoefficient_homogeneousDilation 0 R R hR hR]
  simp only [mul_zero, Real.rpow_zero, Complex.ofReal_one, one_mul, div_self hR.ne']

noncomputable def cutoffVelocitySchwartz (χ : 𝓢(E, ℂ))
    (hχ : HasCompactSupport (χ : E → ℂ)) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (R : ℝ) : 𝓢(E, ℂ) :=
  (hχ.mul_right (f' := fun x => fderiv ℝ Q (R • x) ((R / 2) • x))).toSchwartzMap
    (χ.smooth'.mul (((contDiff_infty_iff_fderiv.mp hQ).2.comp
      (contDiff_id.const_smul R)).clm_apply (contDiff_id.const_smul (R / 2))))

@[simp] theorem cutoffVelocitySchwartz_apply (χ : 𝓢(E, ℂ))
    (hχ : HasCompactSupport (χ : E → ℂ)) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (R : ℝ) (x : E) :
    cutoffVelocitySchwartz χ hχ Q hQ R x = χ x * fderiv ℝ Q (R • x) ((R / 2) • x) := rfl

noncomputable def normalizedCutoffDefectSchwartz (a b R : ℝ) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) : 𝓢(E, ℂ) :=
  let ψ := compactDilationFamily χ hχ Q hQ R
  Complex.I • cutoffVelocitySchwartz χ hχ Q hQ R +
    (((R ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) • Δ ψ +
    (Complex.I * (a : ℂ) + (b : ℂ)) • ψ - schwartzOddPower m ψ

theorem hasCompactSupport_complexCutoff (χ : 𝓢(E, ℝ))
    (hχ : HasCompactSupport (χ : E → ℝ)) :
    HasCompactSupport (χ.postcompCLM Complex.ofRealCLM : E → ℂ) :=
  hχ.comp_left (g := fun r : ℝ => (r : ℂ)) rfl

theorem normalizedCutoffDefectSchwartz_apply (a b R : ℝ) (hR : 0 < R) (m : ℕ)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (x : E) :
    normalizedCutoffDefectSchwartz a b R m (χ.postcompCLM Complex.ofRealCLM)
      (hasCompactSupport_complexCutoff χ hχ) Q hQ x =
      (χ x : ℂ) * stationarySimilarityDefect a b m Q (R • x) +
        cutoffResidual m R χ Q (R • x) := by
  have hφ : (compactDilationFamily (χ.postcompCLM Complex.ofRealCLM)
      (hasCompactSupport_complexCutoff χ hχ) Q hQ R : E → ℂ) =
      fun z => (χ z : ℂ) * Q (R • z) := rfl
  have h := cutoff_normalized_similarity_defect a b R hR m χ χ.smooth' Q hQ x
  simpa only [normalizedCutoffDefectSchwartz, add_apply, sub_apply, smul_apply,
    smul_eq_mul, cutoffVelocitySchwartz_apply, compactDilationFamily_apply,
    SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply,
    SchwartzMap.laplacian_apply, schwartzOddPower_apply, Complex.real_smul, hφ] using h

theorem physicalSchwartzCoefficient_cutoffDefect (a b R : ℝ) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (n : frequencyLattice) :
    physicalSchwartzCoefficient 1 n (normalizedCutoffDefectSchwartz a b R m χ hχ Q hQ) =
      Complex.I * physicalSchwartzCoefficient 1 n (cutoffVelocitySchwartz χ hχ Q hQ R) +
      (-(((R ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * ((‖n‖ ^ 2 : ℝ) : ℂ) +
        Complex.I * (a : ℂ) + (b : ℂ)) *
          physicalSchwartzCoefficient 1 n (compactDilationFamily χ hχ Q hQ R) -
      physicalSchwartzCoefficient 1 n (schwartzOddPower m (compactDilationFamily χ hχ Q hQ R)) := by
  rw [normalizedCutoffDefectSchwartz, map_sub, map_add, map_add,
    map_smul, map_smul, map_smul, physicalSchwartzCoefficient_laplacian]
  simp only [smul_eq_mul]
  ring

end DefocusingNLS

end OAI
