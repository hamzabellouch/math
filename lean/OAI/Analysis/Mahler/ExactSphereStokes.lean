import OAI.Analysis.Mahler.ExactSphereFluxBridge
import OAI.Analysis.Mahler.ClosedBoundaryStokes

namespace OAI

noncomputable section
open Set Metric MeasureTheory
open scoped Topology
namespace Mahler

/-- C1 on an open sphere neighborhood supplies all continuity needed by the
area integral. There is no regularity assumption inside the ball. -/
lemma continuousOn_extDeriv_sphere {k q : ℕ}
    {eta : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin q]→L[ℝ] ℂ}
    {U : Set (ComplexEuclidean (k+1))} (hU : IsOpen U)
    (hSU : sphere 0 1 ⊆ U) (h : ContDiffOn ℝ 1 eta U) :
    ContinuousOn (extDeriv eta) (sphere 0 1) := by
  intro x hx
  have hd := ((h.contDiffAt (hU.mem_nhds (hSU hx))).fderiv_right (m := 0) (by norm_num)).continuousAt
  exact ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℂ (n := q)).continuous.continuousAt.comp hd).continuousWithinAt

/-- Exact C1 transport to the coordinate sphere. This equality
does not assert that the flux vanishes. -/
theorem sphereFlux_extDeriv_eq_coordinateFlux {k : ℕ}
    (eta : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k)]→L[ℝ] ℂ)
    {U : Set (ComplexEuclidean (k+1))} (hU : IsOpen U)
    (hSU : sphere 0 1 ⊆ U) (h : ContDiffOn ℝ 1 eta U) :
    sphereFlux k (fun x => (extDeriv eta x).toAlternatingMap) =
      MahlerStokes.sphereFlux 1 (extDeriv (fluxPullback eta)) := by
  rw [sphereFlux_eq_coordinateFlux _ (continuousOn_extDeriv_sphere hU hSU h)]
  apply MahlerStokes.sphereFlux_congr
  intro x hx
  have hs : fluxCoordinates k x ∈ sphere (0 : ComplexEuclidean (k+1)) 1 := by
    simp only [mem_sphere, dist_zero_right]
    have hh := norm_fluxCoordinates_sq k x
    have hx' : MahlerStokes.radiusSq x = 1 := by simpa using hx
    rw [hx'] at hh
    nlinarith [norm_nonneg (fluxCoordinates k x)]
  exact (extDeriv_fluxPullback ((h.contDiffAt (hU.mem_nhds (hSU hs))).differentiableAt (by norm_num))).symm

/-- The coordinate Stokes theorem for C2 forms. -/
theorem sphereFlux_extDeriv_eq_zero_of_C2 {k : ℕ}
    (eta : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k)]→L[ℝ] ℂ)
    {U : Set (ComplexEuclidean (k+1))} (hU : IsOpen U)
    (hSU : sphere 0 1 ⊆ U) (h : ContDiffOn ℝ 2 eta U) :
    sphereFlux k (fun x => (extDeriv eta x).toAlternatingMap) = 0 := by
  rw [sphereFlux_extDeriv_eq_coordinateFlux eta hU hSU (h.of_le (by norm_num))]
  apply MahlerStokes.sphereFlux_extDeriv_eq_zero 1
    (hU.preimage (fluxCoordinates k).continuous) _ (fluxPullback eta) (contDiffOn_fluxPullback h)
  intro x hx
  apply hSU
  simp only [mem_sphere, dist_zero_right]
  have hh := norm_fluxCoordinates_sq k x
  have hx' : MahlerStokes.radiusSq x = 1 := by simpa using hx
  rw [hx'] at hh
  nlinarith [norm_nonneg (fluxCoordinates k x)]

end Mahler

end

end OAI
