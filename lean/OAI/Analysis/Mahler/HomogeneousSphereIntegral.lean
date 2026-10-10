import OAI.Analysis.Mahler.SphereDensityRestriction
import OAI.Analysis.Mahler.FluxVariation

namespace OAI

open Complex MeasureTheory Metric

namespace Mahler

lemma boundaryFormFin_smul {k : ℕ}
    (a : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ) (c : ℝ)
    (x : ComplexEuclidean (k+1)) :
    boundaryFormFin (c • a) x = (c : ℂ)^(k+1) • boundaryFormFin a x := by
  have ho : (oneForm (c • a) x).toAlternatingMap = (c : ℂ) • (oneForm a x).toAlternatingMap := by
    ext v
    simp [oneForm_apply, Complex.real_smul]
  have hd : (extDeriv (oneForm (c • a)) x).toAlternatingMap =
      (c : ℂ) • (extDeriv (oneForm a) x).toAlternatingMap := by
    rw [oneForm_smul, extDeriv_smul]
    ext v
    simp [Complex.real_smul]
  unfold boundaryFormFin
  rw [ho, hd, wedgePower_smul, wedge_smul_left, wedge_smul_right, smul_smul, ← pow_succ']
  ext v
  rfl

/-- The flux along the one-form deformation. -/
noncomputable def homogeneousPathFlux (k N m : ℕ)
    (G : Fin N → MvPolynomial (Fin (k+1)) ℂ) (t : ℝ) : ℝ :=
  sphereFlux k (boundaryFormFin (alphaPath (polynomialMap G) (coordinateMap (k+1)) m t))

/-- The actual homogeneous endpoint, with no flux-constancy premise. -/
noncomputable def homogeneousSphereFlux (k N : ℕ)
    (G : Fin N → MvPolynomial (Fin (k+1)) ℂ) : ℝ :=
  sphereFlux k (boundaryFormFin (dcLinear (logTau (polynomialMap G))))

lemma alphaPath_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → E → ℂ) (g : κ → E → ℂ) (m : ℕ) :
    alphaPath f g m 0 = (m : ℝ) • dcLinear (logTau g) := by
  funext x
  simp [alphaPath]
  exact zero_smul ℝ (betaLinear f g m x)

lemma alphaPath_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → E → ℂ) (g : κ → E → ℂ) (m : ℕ) :
    alphaPath f g m 1 = dcLinear (logTau f) := by
  funext x
  simp [alphaPath, betaLinear]

theorem homogeneousPathFlux_zero (k N m : ℕ)
    (G : Fin N → MvPolynomial (Fin (k+1)) ℂ) :
    homogeneousPathFlux k N m G 0 = (Real.pi * (m : ℝ))^(k+1) := by
  unfold homogeneousPathFlux sphereFlux
  simp only [alphaPath_zero, boundaryFormFin_smul]
  have he : (fun x : sphere (0 : ComplexEuclidean (k+1)) 1 =>
      (orientedDensity (sphereFrame k) (sphereVolume k)
        ((↑(m : ℝ) : ℂ)^(k+1) • boundaryFormFin (dcLinear (logTau (coordinateMap (k+1)))) x) x).re) =
      (fun x : sphere (0 : ComplexEuclidean (k+1)) 1 =>
        (m : ℝ)^(k+1) * (orientedDensity (sphereFrame k) (sphereVolume k)
          (boundaryFormFin (dcLinear (logTau (coordinateMap (k+1)))) x) x).re) := by
    funext x
    rw [orientedDensity_smul, ← Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [he, integral_const_mul]
  change (m : ℝ)^(k+1) * sphereFlux k (boundaryFormFin (dcLinear (logTau (coordinateMap (k+1))))) = _
  rw [reference_boundary_flux, mul_pow, mul_comm]

lemma homogeneousPathFlux_one (k N m : ℕ)
    (G : Fin N → MvPolynomial (Fin (k+1)) ℂ) :
    homogeneousPathFlux k N m G 1 = homogeneousSphereFlux k N G := by
  simp only [homogeneousPathFlux, homogeneousSphereFlux, alphaPath_one]

end Mahler

end OAI
