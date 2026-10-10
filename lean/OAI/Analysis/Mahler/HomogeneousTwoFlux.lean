import OAI.Analysis.Mahler.ExactSphereStokes
import OAI.Analysis.Mahler.HomogeneousTwoTransgression
import OAI.Analysis.Mahler.HomogeneousFluxFTC
import OAI.Analysis.Mahler.SphereDensityBridge

namespace OAI

noncomputable section
open Set Metric MeasureTheory
open scoped Topology
namespace Mahler

theorem MassHypotheses.homogeneousTwoPrimitive_C2 {N m : ℕ}
    {U : Set (ComplexEuclidean 2)} {f : Fin N → ComplexEuclidean 2 → ℂ}
    {G : Fin N → MvPolynomial (Fin 2) ℂ} (h : MassHypotheses 2 N m U f G) (t : ℝ) :
    ContDiffOn ℝ 2 (homogeneousTwoPrimitive (m := m) G t) ({0}ᶜ) := by
  intro x hx
  have hs := h.alpha_beta_contDiffAt (by simpa using hx) t 2
  exact (contDiffAt_pairExterior 2 hs.1 hs.2).contDiffWithinAt

/-- The closed-sphere integral of the dimension-two primitive vanishes.
C2 follows from the mass hypotheses; it is not an added premise. -/
theorem MassHypotheses.homogeneousTwoPrimitive_flux_zero {N m : ℕ}
    {U : Set (ComplexEuclidean 2)} {f : Fin N → ComplexEuclidean 2 → ℂ}
    {G : Fin N → MvPolynomial (Fin 2) ℂ} (h : MassHypotheses 2 N m U f G) (t : ℝ) :
    sphereFlux 1 (fun x => (extDeriv (homogeneousTwoPrimitive (m := m) G t) x).toAlternatingMap) = 0 := by
  apply sphereFlux_extDeriv_eq_zero_of_C2 _ isOpen_compl_singleton _
    (h.homogeneousTwoPrimitive_C2 t)
  intro x hx
  have hn : ‖x‖ = 1 := by simpa using hx
  simpa only [mem_compl_iff, mem_singleton_iff] using
    (show x ≠ 0 from by intro he; simp [he] at hn)

theorem MassHypotheses.homogeneousResidualFlux_two_eq_zero {N m : ℕ}
    {U : Set (ComplexEuclidean 2)} {f : Fin N → ComplexEuclidean 2 → ℂ}
    {G : Fin N → MvPolynomial (Fin 2) ℂ} (h : MassHypotheses 2 N m U f G) (t : ℝ) :
    sphereFlux 1 (boundaryResidualFin
      (alphaPath (polynomialMap G) (coordinateMap 2) m t)
      (betaLinear (polynomialMap G) (coordinateMap 2) m)) = 0 := by
  have he : sphereFlux 1 (boundaryResidualFin
      (alphaPath (polynomialMap G) (coordinateMap 2) m t)
      (betaLinear (polynomialMap G) (coordinateMap 2) m)) =
      -sphereFlux 1 (fun x => (extDeriv (homogeneousTwoPrimitive (m := m) G t) x).toAlternatingMap) := by
    unfold sphereFlux
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    have hx : ‖(x : ComplexEuclidean 2)‖ = 1 := by simp
    have hn : (x : ComplexEuclidean 2) ≠ 0 := by intro he; simp [he] at hx
    have hd := orientedDensity_congr_on_tangent (k := 1) hx
      (B := boundaryResidualFin
        (alphaPath (polynomialMap G) (coordinateMap 2) m t)
        (betaLinear (polynomialMap G) (coordinateMap 2) m) x)
      (C := -(extDeriv (homogeneousTwoPrimitive (m := m) G t) x).toAlternatingMap)
      (fun v hv => h.sphere_residual_two_transgression hn t v hv)
    rw [hd]
    rw [← neg_one_smul ℂ (extDeriv (homogeneousTwoPrimitive (m := m) G t) x).toAlternatingMap,
      orientedDensity_smul]
    simp
  rw [he, h.homogeneousTwoPrimitive_flux_zero t, neg_zero]

/-- The actual homogeneous flux is constant on the whole parameter line in
complex dimension two. No integral identity remains as a premise. -/
theorem MassHypotheses.homogeneousPathFlux_two_constant {N m : ℕ}
    {U : Set (ComplexEuclidean 2)} {f : Fin N → ComplexEuclidean 2 → ℂ}
    {G : Fin N → MvPolynomial (Fin 2) ℂ} (h : MassHypotheses 2 N m U f G) (a b : ℝ) :
    homogeneousPathFlux 1 N m G b = homogeneousPathFlux 1 N m G a := by
  have he := h.homogeneousPathFlux_sub_eq_integral (k := 1) a b
  simp_rw [h.homogeneousResidualFlux_two_eq_zero] at he
  exact sub_eq_zero.mp (by simpa using he)

/-- The homogeneous unit-sphere value in complex dimension two. -/
theorem MassHypotheses.homogeneousSphereFlux_two_value {N m : ℕ}
    {U : Set (ComplexEuclidean 2)} {f : Fin N → ComplexEuclidean 2 → ℂ}
    {G : Fin N → MvPolynomial (Fin 2) ℂ} (h : MassHypotheses 2 N m U f G) :
    homogeneousSphereFlux 1 N G = (Real.pi * (m : ℝ))^2 := by
  simpa only [homogeneousPathFlux_one, homogeneousPathFlux_zero] using
    h.homogeneousPathFlux_two_constant 0 1

/-- The radius-sphere flux limit in complex
dimension two, from MassHypotheses alone. -/
theorem MassHypotheses.small_sphere_real_flux_limit_two {N m : ℕ}
    {U : Set (ComplexEuclidean 2)} {f : Fin N → ComplexEuclidean 2 → ℂ}
    {G : Fin N → MvPolynomial (Fin 2) ℂ} (h : MassHypotheses 2 N m U f G) :
    Filter.Tendsto (fun r => (radiusSphereFlux 1 (logTau f) r).re)
      (nhdsWithin 0 (Ioi 0)) (nhds ((Real.pi * (m : ℝ))^2)) := by
  simpa only [h.homogeneousSphereFlux_two_value] using h.small_sphere_real_flux_limit (k := 1)

end Mahler

end

end OAI
