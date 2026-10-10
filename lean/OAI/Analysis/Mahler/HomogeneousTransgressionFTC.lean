import OAI.Analysis.Mahler.SourcePrimitiveStokes
import OAI.Analysis.Mahler.HomogeneousFluxFTC
import OAI.Analysis.Mahler.SphereDensityBridge
import OAI.Analysis.Mahler.HomogeneousCircleIntegral

namespace OAI

open Complex Set Metric
open scoped Topology

noncomputable section
namespace Mahler

theorem MassHypotheses.homogeneousResidualFlux_eq_zero_of_transgression {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    (t : ℝ)
    (ht : ∀ x : ComplexEuclidean (k+2), ‖x‖ = 1 →
      ∀ v : Fin (2*(k+1)+1) → ComplexEuclidean (k+2),
      (∀ i, inner ℝ x (v i) = 0) →
      boundaryResidualFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x v =
        -((k+1 : ℕ) : ℂ) * extDeriv (sourceHomogeneousPrimitive (m := m) G t) x v) :
    sphereFlux (k+1) (boundaryResidualFin
      (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
      (betaLinear (polynomialMap G) (coordinateMap (k+2)) m)) = 0 := by
  apply sphereFlux_eq_zero_of_tangent_exact_C2 _
    (sourceHomogeneousPrimitive (m := m) G t) (-((k+1 : ℕ) : ℝ))
    (h.sourceHomogeneousPrimitive_C2 t)
  simpa only [Complex.ofReal_neg, Complex.ofReal_natCast] using ht

/-- The fundamental theorem of calculus with an explicit local transgression formula.
The local algebraic identity is retained as a conditional premise. -/
theorem MassHypotheses.homogeneousPathFlux_constant_of_transgression {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    (ht : ∀ (t : ℝ) (x : ComplexEuclidean (k+2)), ‖x‖ = 1 →
      ∀ v : Fin (2*(k+1)+1) → ComplexEuclidean (k+2),
      (∀ i, inner ℝ x (v i) = 0) →
      boundaryResidualFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x v =
        -((k+1 : ℕ) : ℂ) * extDeriv (sourceHomogeneousPrimitive (m := m) G t) x v)
    (a b : ℝ) : homogeneousPathFlux (k+1) N m G b = homogeneousPathFlux (k+1) N m G a := by
  have he := h.homogeneousPathFlux_sub_eq_integral (k := k+1) a b
  have hz (t : ℝ) := h.homogeneousResidualFlux_eq_zero_of_transgression t (ht t)
  simp_rw [hz] at he
  exact sub_eq_zero.mp (by simpa using he)

/-- Both flux endpoints follow from the explicit local formula.
This theorem retains the local transgression identity as a hypothesis. -/
theorem MassHypotheses.homogeneousFlux_endpoints_of_transgression {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    (ht : ∀ (t : ℝ) (x : ComplexEuclidean (k+2)), ‖x‖ = 1 →
      ∀ v : Fin (2*(k+1)+1) → ComplexEuclidean (k+2),
      (∀ i, inner ℝ x (v i) = 0) →
      boundaryResidualFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x v =
        -((k+1 : ℕ) : ℂ) * extDeriv (sourceHomogeneousPrimitive (m := m) G t) x v) :
    homogeneousSphereFlux (k+1) N G = (Real.pi * (m : ℝ))^(k+2) ∧
    Filter.Tendsto (fun r => (radiusSphereFlux (k+1) (logTau f) r).re)
      (nhdsWithin 0 (Ioi 0)) (nhds ((Real.pi * (m : ℝ))^(k+2))) := by
  have hv : homogeneousSphereFlux (k+1) N G = (Real.pi * (m : ℝ))^(k+2) := by
    simpa only [homogeneousPathFlux_one, homogeneousPathFlux_zero] using
      h.homogeneousPathFlux_constant_of_transgression ht 0 1
  exact ⟨hv, by simpa only [hv] using h.small_sphere_real_flux_limit (k := k+1)⟩

theorem MassHypotheses.small_sphere_real_flux_limit_one {N m : ℕ}
    {U : Set (ComplexEuclidean 1)} {f : Fin N → ComplexEuclidean 1 → ℂ}
    {G : Fin N → MvPolynomial (Fin 1) ℂ} (h : MassHypotheses 1 N m U f G) :
    Filter.Tendsto (fun r => (radiusSphereFlux 0 (logTau f) r).re)
      (nhdsWithin 0 (Ioi 0)) (nhds (Real.pi * (m : ℝ))) := by
  simpa only [h.homogeneousCircle_flux] using h.small_sphere_real_flux_limit (k := 0)

end Mahler

end

end OAI
