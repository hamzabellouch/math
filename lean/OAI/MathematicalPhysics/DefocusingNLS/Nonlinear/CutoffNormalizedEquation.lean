import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffTransport

namespace OAI

/-! # The cutoff defect in the fixed normalized spatial coordinate -/

open scoped Laplacian ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem laplacian_complex_dilation (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (r : ℝ) (x : E) :
    Δ (fun y => f (r • y)) x = (r ^ (2 : ℕ) : ℝ) • Δ f (r • x) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 12) ℝ)]
  have hd : iteratedFDeriv ℝ 2 (fun y => f (r • y)) x =
      r ^ (2 : ℕ) • iteratedFDeriv ℝ 2 f (r • x) := by
    simpa only using! congrFun (iteratedFDeriv_comp_const_smul r
      (hf.of_le (by simp : (2 : ℕ∞ω) ≤ ∞))) x
  rw [hd, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_apply]

/-- Exact fixed-coordinate equation, with both the profile defect and cutoff residual visible. -/
theorem cutoff_normalized_similarity_defect (a b R : ℝ) (hR : 0 < R) (m : ℕ)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (x : E) :
    Complex.I * ((χ x : ℂ) * fderiv ℝ Q (R • x) ((R / 2) • x)) +
      ((R ^ (2 : ℕ))⁻¹ : ℝ) • Δ (fun z => (χ z : ℂ) * Q (R • z)) x +
      (Complex.I * (a : ℂ) + (b : ℂ)) * ((χ x : ℂ) * Q (R • x)) -
      oddPowerNonlinearity m ((χ x : ℂ) * Q (R • x)) =
        (χ x : ℂ) * stationarySimilarityDefect a b m Q (R • x) +
          cutoffResidual m R χ Q (R • x) := by
  let ψ : E → ℂ := fun y => (χ (R⁻¹ • y) : ℂ) * Q y
  have hψ : ContDiff ℝ ∞ ψ :=
    (Complex.ofRealCLM.contDiff.comp (hχ.comp (contDiff_id.const_smul R⁻¹))).mul hQ
  have hscale : (fun z => (χ z : ℂ) * Q (R • z)) = fun z => ψ (R • z) := by
    funext z
    simp only [ψ, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  have hlap : ((R ^ (2 : ℕ))⁻¹ : ℝ) •
      Δ (fun z => (χ z : ℂ) * Q (R • z)) x = Δ ψ (R • x) := by
    rw [hscale, laplacian_complex_dilation ψ hψ, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero _ hR.ne'), one_smul]
  have harg : R⁻¹ • (R • x) = x := by
    rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  have hsp := cutoffResidual_spatial_identity m R χ Q hχ hQ (R • x)
  rw [harg] at hsp
  change Δ ψ (R • x) - oddPowerNonlinearity m ((χ x : ℂ) * Q (R • x)) = _ at hsp
  have hvec : (1 / 2 : ℝ) • (R • x) = (R / 2) • x := by
    rw [smul_smul]
    congr 1
    ring
  rw [hlap]
  unfold stationarySimilarityDefect
  rw [hvec]
  linear_combination hsp

end DefocusingNLS

end OAI
