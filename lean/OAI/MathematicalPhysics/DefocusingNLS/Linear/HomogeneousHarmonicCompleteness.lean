import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPolynomialHarmonic
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicWeakLaplacian

namespace OAI

/-! # A nonzero physical function has a nonzero spherical harmonic coefficient

Polynomial density and harmonic decomposition give the exact completeness
consequence needed for the finite-dimensional spectral classification.
-/

open Set MeasureTheory
open scoped ContDiff Laplacian

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem continuous_exists_nonzero_away_origin (F : E → ℂ) (hF : Continuous F)
    (hne : F ≠ 0) : ∃ x : E, x ≠ 0 ∧ F x ≠ 0 := by
  by_contra! h
  apply hne
  exact Continuous.ext_on (dense_compl_singleton (0 : E)) hF continuous_const
    (fun x hx => h x (by simpa only [mem_compl_iff, mem_singleton_iff] using hx))

theorem physical_exists_nonzero_harmonic_coefficient (F : E → ℂ)
    (hF : Continuous F) (hne : F ≠ 0) :
    ∃ (p : PhysicalRealPolynomial) (ell : ℕ) (r : ℝ),
      p.IsHomogeneous ell ∧ physicalPolynomialLaplacian p = 0 ∧ 0 < r ∧
      harmonicAngularCoefficient (physicalHarmonicExtension p ell) F r ≠ 0 := by
  obtain ⟨x, hx, hFx⟩ := continuous_exists_nonzero_away_origin F hF hne
  let r := ‖x‖
  have hr : 0 < r := norm_pos_iff.mpr hx
  let f : C(PhysicalUnitSphere, ℂ) :=
    ⟨fun z => F (r • z.1), by fun_prop⟩
  have hf : f ≠ 0 := by
    intro hf
    let z : PhysicalUnitSphere := ⟨r⁻¹ • x, by
      simp only [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hr, r, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
    have hz := DFunLike.congr_fun hf z
    apply hFx
    simpa only [f, z, ContinuousMap.coe_mk, smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
      ContinuousMap.zero_apply] using hz
  obtain ⟨p, ell, hp, hDp, hm⟩ := physicalSphere_exists_harmonic_polynomial_moment f hf
  refine ⟨p, ell, r, hp, hDp, hr, ?_⟩
  simpa only [harmonicAngularCoefficient, physicalHarmonicExtension_sphere, f,
    ContinuousMap.coe_mk] using hm

theorem physical_exists_spherical_eigenfunction (F : E → ℂ)
    (hF : Continuous F) (hne : F ≠ 0) :
    ∃ (ell : ℕ) (Y : E → ℂ) (r : ℝ),
      (∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x) ∧
      (∀ (x : E) (t : ℝ), 0 < t → Y (t • x) = Y x) ∧
      (∀ x : E, x ≠ 0 → Δ Y x =
        -(((ell : ℂ) * (ell + 10)) / (‖x‖ ^ 2 : ℝ)) * Y x) ∧
      0 < r ∧ harmonicAngularCoefficient Y F r ≠ 0 := by
  obtain ⟨p, ell, r, hp, hDp, hr, hm⟩ :=
    physical_exists_nonzero_harmonic_coefficient F hF hne
  exact ⟨ell, physicalHarmonicExtension p ell, r,
    physicalHarmonicExtension_contDiffAt p ell, physicalHarmonicExtension_ray p ell hp,
    physicalHarmonicExtension_laplacian p ell hp hDp, hr, hm⟩

theorem physical_pair_exists_spherical_eigenfunction (F G : E → ℂ)
    (hF : Continuous F) (hG : Continuous G)
    (hne : ∃ x : E, F x ≠ 0 ∨ G x ≠ 0) :
    ∃ (ell : ℕ) (Y : E → ℂ) (r : ℝ),
      (∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x) ∧
      (∀ (x : E) (t : ℝ), 0 < t → Y (t • x) = Y x) ∧
      (∀ x : E, x ≠ 0 → Δ Y x =
        -(((ell : ℂ) * (ell + 10)) / (‖x‖ ^ 2 : ℝ)) * Y x) ∧
      0 < r ∧ (harmonicAngularCoefficient Y F r ≠ 0 ∨
        harmonicAngularCoefficient Y G r ≠ 0) := by
  obtain ⟨x, hx⟩ := hne
  rcases hx with hx | hx
  · have hF0 : F ≠ 0 := fun h => hx (congrFun h x)
    obtain ⟨ell, Y, r, hYs, hYr, hYe, hr, hm⟩ :=
      physical_exists_spherical_eigenfunction F hF hF0
    exact ⟨ell, Y, r, hYs, hYr, hYe, hr, Or.inl hm⟩
  · have hG0 : G ≠ 0 := fun h => hx (congrFun h x)
    obtain ⟨ell, Y, r, hYs, hYr, hYe, hr, hm⟩ :=
      physical_exists_spherical_eigenfunction G hG hG0
    exact ⟨ell, Y, r, hYs, hYr, hYe, hr, Or.inr hm⟩

end DefocusingNLS

end OAI
