import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpherePolynomial
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicDecomposition

namespace OAI

/-! # Harmonic polynomial restrictions span the sphere polynomials -/

open Set MeasureTheory MvPolynomial

namespace DefocusingNLS

def physicalHarmonicPolynomialRestrictions : Set C(PhysicalUnitSphere, ℝ) :=
  {f | ∃ (p : PhysicalRealPolynomial) (n : ℕ), p.IsHomogeneous n ∧
    physicalPolynomialLaplacian p = 0 ∧ physicalSpherePolynomial p = f}

noncomputable def physicalHarmonicPolynomialSpan : Submodule ℝ C(PhysicalUnitSphere, ℝ) :=
  Submodule.span ℝ physicalHarmonicPolynomialRestrictions

theorem physicalSpherePolynomial_radius :
    physicalSpherePolynomial physicalRadiusPolynomial = 1 := by
  ext z
  rw [physicalSpherePolynomial_apply]
  simp only [physicalRadiusPolynomial, map_sum, map_pow, MvPolynomial.eval_X,
    ContinuousMap.one_apply]
  rw [← EuclideanSpace.real_norm_sq_eq]
  have hz : ‖z.1‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using z.2
  rw [hz, one_pow]

theorem physicalSpherePolynomial_homogeneous_mem_span (p : PhysicalRealPolynomial)
    (n : ℕ) (hp : p.IsHomogeneous n) :
    physicalSpherePolynomial p ∈ physicalHarmonicPolynomialSpan := by
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hn : n ≤ 1
    · apply Submodule.subset_span
      exact ⟨p, n, hp, physicalPolynomialLaplacian_low_degree p n hp hn, rfl⟩
    obtain ⟨h, q, hh, hDh, hq, he⟩ := physicalPolynomial_harmonic_decomposition p n hp
    rw [he, map_add, map_mul, physicalSpherePolynomial_radius, one_mul]
    apply Submodule.add_mem
    · exact Submodule.subset_span ⟨h, n, hh, hDh, rfl⟩
    · exact ih (n - 2) (by omega) q hq

theorem physicalSpherePolynomial_mem_harmonic_span (p : PhysicalRealPolynomial) :
    physicalSpherePolynomial p ∈ physicalHarmonicPolynomialSpan := by
  rw [← MvPolynomial.sum_homogeneousComponent p, map_sum]
  apply Submodule.sum_mem
  intro n _
  exact physicalSpherePolynomial_homogeneous_mem_span _ n
    (MvPolynomial.homogeneousComponent_isHomogeneous n p)

noncomputable def physicalSphereMoment (f : C(PhysicalUnitSphere, ℂ)) :
    C(PhysicalUnitSphere, ℝ) →ₗ[ℝ] ℂ where
  toFun g := ∫ z, (g z : ℂ) * f z ∂physicalSphereMeasure
  map_add' g h := by
    have hg : Integrable (fun z => (g z : ℂ) * f z) physicalSphereMeasure :=
      ((Complex.continuous_ofReal.comp g.continuous).mul f.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hh : Integrable (fun z => (h z : ℂ) * f z) physicalSphereMeasure :=
      ((Complex.continuous_ofReal.comp h.continuous).mul f.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    simp only [ContinuousMap.add_apply, Complex.ofReal_add, add_mul]
    exact integral_add hg hh
  map_smul' c g := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.ofReal_mul,
      mul_assoc]
    exact integral_const_mul _ _

theorem physicalSphere_eq_zero_of_harmonic_polynomial_moments
    (f : C(PhysicalUnitSphere, ℂ))
    (hf : ∀ (p : PhysicalRealPolynomial) (n : ℕ), p.IsHomogeneous n →
      physicalPolynomialLaplacian p = 0 →
      (∫ z, (physicalSpherePolynomial p z : ℂ) * f z ∂physicalSphereMeasure) = 0) : f = 0 := by
  have hspan : physicalHarmonicPolynomialSpan ≤ (physicalSphereMoment f).ker := by
    apply Submodule.span_le.mpr
    rintro g ⟨p, n, hp, hDp, rfl⟩
    exact hf p n hp hDp
  apply physicalSphere_eq_zero_of_polynomial_moments
  intro p
  exact hspan (physicalSpherePolynomial_mem_harmonic_span p)

theorem physicalSphere_exists_harmonic_polynomial_moment
    (f : C(PhysicalUnitSphere, ℂ)) (hf : f ≠ 0) :
    ∃ (p : PhysicalRealPolynomial) (n : ℕ), p.IsHomogeneous n ∧
      physicalPolynomialLaplacian p = 0 ∧
      (∫ z, (physicalSpherePolynomial p z : ℂ) * f z ∂physicalSphereMeasure) ≠ 0 := by
  by_contra! h
  exact hf (physicalSphere_eq_zero_of_harmonic_polynomial_moments f h)

end DefocusingNLS

end OAI
