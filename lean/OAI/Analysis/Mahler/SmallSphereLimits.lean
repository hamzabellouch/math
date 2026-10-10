import OAI.Analysis.Mahler.RealLogBridge
import OAI.Analysis.Mahler.SphereOrientation
import OAI.Analysis.Mahler.StripRegularLevels

namespace OAI

open MeasureTheory Metric Filter
open scoped Topology
namespace Mahler

/-- The small-sphere limit of Bochner integrals
on varying radius spheres, under the mass hypotheses alone. -/
theorem MassHypotheses.small_sphere_surface_integral_limit {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    Tendsto (radiusSphereFlux k (logTau f)) (𝓝[>] 0)
      (𝓝 (unitSphereFlux k (logTau (polynomialMap G)))) := by
  apply h.small_sphere_flux_limit.congr'
  filter_upwards [self_mem_nhdsWithin, h.eventually_sphereAnnulus_log_regular] with r hr hreg
  symm
  apply radiusSphereFlux_eq_small r hr
  intro z
  obtain ⟨w, hw⟩ := sphereDilation_surjective r hr z
  have he : r • (w : ComplexEuclidean (k+1)) = z := congrArg Subtype.val hw
  rw [← he]
  exact (hreg w (sphere_subset_annulus _ w.property)).2.2

/-- Dimension-indexed surface flux, including an irrelevant zero-dimensional branch. -/
noncomputable def massSphereFlux : (n : ℕ) → (ComplexEuclidean n → ℂ) → ℝ → ℂ
  | 0, _, _ => 0
  | k+1, u, r => radiusSphereFlux k u r

noncomputable def massUnitSphereFlux : (n : ℕ) → (ComplexEuclidean n → ℂ) → ℂ
  | 0, _ => 0
  | k+1, u => unitSphereFlux k u

/-- The small-sphere limit in the full dimension variable, with the
mass hypotheses and no added analytic convergence assumptions. -/
theorem MassHypotheses.mass_small_sphere_limit {n N m : ℕ}
    {U : Set (ComplexEuclidean n)} {f : Fin N → ComplexEuclidean n → ℂ}
    {G : Fin N → MvPolynomial (Fin n) ℂ} (h : MassHypotheses n N m U f G) :
    Tendsto (massSphereFlux n (logTau f)) (𝓝[>] 0)
      (𝓝 (massUnitSphereFlux n (logTau (polynomialMap G)))) := by
  cases n with
  | zero => have hn := h.dimension_pos; omega
  | succ k => exact h.small_sphere_surface_integral_limit

end Mahler

end OAI
