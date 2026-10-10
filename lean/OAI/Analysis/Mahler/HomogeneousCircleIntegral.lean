import OAI.Analysis.Mahler.HomogeneousDensityVariation
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

open Complex MeasureTheory Metric

namespace Mahler

lemma wedge_zero_right {T ι κ : Type*} [AddCommGroup T] [Module ℝ T]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (a : T [⋀^ι]→ₗ[ℝ] ℂ) : wedge a (0 : T [⋀^κ]→ₗ[ℝ] ℂ) = 0 := by
  have h := wedge_sum_right (∅ : Finset ℕ) a (fun _ => (0 : T [⋀^κ]→ₗ[ℝ] ℂ))
  simpa only [Finset.sum_empty] using h

lemma boundaryResidualFin_zero_dim
    (a b : ComplexEuclidean 1 → ComplexEuclidean 1 →L[ℝ] ℂ) (x : ComplexEuclidean 1) :
    boundaryResidualFin (k := 0) a b x = 0 := by
  simp [boundaryResidualFin, wedgePowerVariation, wedge_zero_right]

/-- In complex dimension one there is no residual term. This is actual
pointwise constancy of the oriented density, not an integral assumption. -/
theorem MassHypotheses.circle_density_const {N m : ℕ}
    {U : Set (ComplexEuclidean 1)} {f : Fin N → ComplexEuclidean 1 → ℂ}
    {G : Fin N → MvPolynomial (Fin 1) ℂ} (h : MassHypotheses 1 N m U f G)
    {x : ComplexEuclidean 1} (hx : ‖x‖ = 1) (s t : ℝ) :
    orientedDensity (sphereFrame 0) (sphereVolume 0)
      (boundaryFormFin (alphaPath (polynomialMap G) (coordinateMap 1) m s) x) x =
    orientedDensity (sphereFrame 0) (sphereVolume 0)
      (boundaryFormFin (alphaPath (polynomialMap G) (coordinateMap 1) m t) x) x := by
  have hd (r : ℝ) : HasDerivAt
      (fun q => orientedDensity (sphereFrame 0) (sphereVolume 0)
        (boundaryFormFin (alphaPath (polynomialMap G) (coordinateMap 1) m q) x) x) 0 r := by
    simpa only [boundaryResidualFin_zero_dim, orientedDensity_zero] using h.sphere_density_derivative hx r
  exact is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) s t

/-- Actual homogeneous flux constancy in dimension one, proved without
integration by parts because the residual degree is zero. The higher-
dimensional residual is not eliminated by this theorem. -/
theorem MassHypotheses.circle_flux_const {N m : ℕ}
    {U : Set (ComplexEuclidean 1)} {f : Fin N → ComplexEuclidean 1 → ℂ}
    {G : Fin N → MvPolynomial (Fin 1) ℂ} (h : MassHypotheses 1 N m U f G)
    (s t : ℝ) : homogeneousPathFlux 0 N m G s = homogeneousPathFlux 0 N m G t := by
  unfold homogeneousPathFlux sphereFlux
  apply integral_congr_ae
  filter_upwards [] with x
  apply congrArg Complex.re
  exact h.circle_density_const (by simpa only [mem_sphere_iff_norm, sub_zero] using x.property) s t

/-- Full homogeneous sphere normalization for complex dimension one. -/
theorem MassHypotheses.homogeneousCircle_flux {N m : ℕ}
    {U : Set (ComplexEuclidean 1)} {f : Fin N → ComplexEuclidean 1 → ℂ}
    {G : Fin N → MvPolynomial (Fin 1) ℂ} (h : MassHypotheses 1 N m U f G) :
    homogeneousSphereFlux 0 N G = Real.pi * (m : ℝ) := by
  rw [← homogeneousPathFlux_one 0 N m G, h.circle_flux_const 1 0, homogeneousPathFlux_zero]
  simp

end Mahler

end OAI
