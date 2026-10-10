import OAI.Analysis.Mahler.HomogeneousFluxDifferentiation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

open Complex MeasureTheory Metric Set Filter
open scoped Topology

namespace Mahler

/-- The residual flux is continuous on the entire parameter line. -/
theorem MassHypotheses.homogeneousResidualFlux_continuous {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    Continuous (fun t => sphereFlux k (boundaryResidualFin
      (alphaPath (polynomialMap G) (coordinateMap (k+1)) m t)
      (betaLinear (polynomialMap G) (coordinateMap (k+1)) m))) := by
  obtain ⟨ha, hb⟩ := h.homogeneous_path_C1
  exact sphereFlux_continuous (continuous_sphere_affine_residual_eval ha hb)

/-- A finite, integrated variation formula for the literal homogeneous path.
This supplies endpoint control as well as the pointwise derivative. The exact
residual integral is not replaced by zero. -/
theorem MassHypotheses.homogeneousPathFlux_sub_eq_integral {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G)
    (a b : ℝ) :
    homogeneousPathFlux k N m G b - homogeneousPathFlux k N m G a =
      ∫ t in a..b, sphereFlux k (boundaryResidualFin
        (alphaPath (polynomialMap G) (coordinateMap (k+1)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+1)) m)) := by
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => h.homogeneousPathFlux_hasDerivAt t)
    (h.homogeneousResidualFlux_continuous.intervalIntegrable a b)).symm

/-- Actual endpoint discrepancy from the reference value, with only the
remaining integrated residual on the right-hand side. -/
theorem MassHypotheses.homogeneousSphereFlux_sub_reference {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    homogeneousSphereFlux k N G - (Real.pi * (m : ℝ))^(k+1) =
      ∫ t in (0 : ℝ)..1, sphereFlux k (boundaryResidualFin
        (alphaPath (polynomialMap G) (coordinateMap (k+1)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+1)) m)) := by
  simpa only [homogeneousPathFlux_one, homogeneousPathFlux_zero] using
    h.homogeneousPathFlux_sub_eq_integral 0 1

end Mahler

end OAI
