import OAI.Analysis.Mahler.SphereFlux

namespace OAI

open MeasureTheory Metric Set
open scoped ENNReal

namespace Mahler

/-- Positive dilation sends the unit sphere to the radius-r sphere. -/
noncomputable def sphereDilation {n : ℕ} (r : ℝ) (hr : 0 < r) :
    sphere (0 : ComplexEuclidean n) 1 → sphere (0 : ComplexEuclidean n) r := fun z =>
  ⟨r • (z : ComplexEuclidean n), by
    have hz : ‖(z : ComplexEuclidean n)‖ = 1 := by simp
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hz]⟩

lemma continuous_sphereDilation {n : ℕ} (r : ℝ) (hr : 0 < r) :
    Continuous (sphereDilation (n := n) r hr) := by
  apply continuous_induced_rng.2
  change Continuous (fun z : sphere (0 : ComplexEuclidean n) 1 => r • (z : ComplexEuclidean n))
  exact (continuous_const : Continuous (fun _ : sphere (0 : ComplexEuclidean n) 1 => r)).smul
    (continuous_subtype_val : Continuous (fun z : sphere (0 : ComplexEuclidean n) 1 => (z : ComplexEuclidean n)))

lemma positive_dilation_outward_normal {n : ℕ} (r : ℝ) (hr : 0 < r)
    (z : sphere (0 : ComplexEuclidean n) 1) :
    ‖r • (z : ComplexEuclidean n)‖⁻¹ • (r • (z : ComplexEuclidean n)) = z := by
  have hz : ‖(z : ComplexEuclidean n)‖ = 1 := by simp
  simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hz, smul_smul, hr.ne']

/-- The derivative restricted to an oriented d-dimensional tangent frame has
positive determinant r^d. This fixes both the surface Jacobian and its sign. -/
theorem positive_dilation_surface_determinant (d : ℕ) (r : ℝ) (hr : 0 < r) :
    Matrix.det (r • (1 : Matrix (Fin d) (Fin d) ℝ)) = r^d ∧ 0 < r^d := by
  constructor
  · simp
  · exact pow_pos hr d

/-- Euclidean sphere area at radius r, transported from the volume-induced
unit sphere measure with its positive tangential Jacobian. -/
noncomputable def radiusSphereArea (n : ℕ) (r : ℝ) (hr : 0 < r) :
    Measure (sphere (0 : ComplexEuclidean n) r) :=
  ENNReal.ofReal (r^(2*n-1)) • (sphereArea n).map (sphereDilation r hr)

/-- The surface measure change of variables for an actual Bochner integral. -/
theorem integral_radiusSphereArea {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : sphere (0 : ComplexEuclidean n) r → ℂ)
    (hg : AEStronglyMeasurable g ((sphereArea n).map (sphereDilation r hr))) :
    (∫ z, g z ∂radiusSphereArea n r hr) =
      (r^(2*n-1)) • ∫ z : sphere (0 : ComplexEuclidean n) 1,
        g (sphereDilation r hr z) ∂sphereArea n := by
  rw [radiusSphereArea, integral_smul_measure, integral_map
    (continuous_sphereDilation r hr).aemeasurable hg]
  rw [ENNReal.toReal_ofReal (le_of_lt (pow_pos hr _))]

/-- The parameterized flux is also an integral on the actual radius-r sphere,
with its outward normal and Euclidean area measure. -/
theorem smallSphereFlux_eq_radiusIntegral {k : ℕ} (u : ComplexEuclidean (k+1) → ℂ)
    (r : ℝ) (hr : 0 < r)
    (hg : AEStronglyMeasurable
      (fun z : sphere (0 : ComplexEuclidean (k+1)) r =>
        sphereDensity k (r⁻¹ • (z : ComplexEuclidean (k+1))) (boundaryForm u k z))
      ((sphereArea (k+1)).map (sphereDilation r hr))) :
    smallSphereFlux k u r =
      ∫ z : sphere (0 : ComplexEuclidean (k+1)) r,
        sphereDensity k (r⁻¹ • (z : ComplexEuclidean (k+1))) (boundaryForm u k z)
          ∂radiusSphereArea (k+1) r hr := by
  rw [integral_radiusSphereArea r hr _ hg, ← integral_smul]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  have he : 2*(k+1)-1 = 2*k+1 := by omega
  simp only [sphereDilation, he, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  simp [Complex.real_smul]

end Mahler

end OAI
