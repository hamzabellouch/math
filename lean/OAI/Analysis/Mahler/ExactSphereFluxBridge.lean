import OAI.Analysis.Mahler.ExactFormCoordinates
import OAI.Analysis.Mahler.SphereCoordinateIntegral

namespace OAI

noncomputable section
open Set Metric MeasureTheory
open scoped Topology BigOperators
namespace Mahler

/-- The real coordinate cofactor sum is the actual complex sphereFlux density.
The volume of the chosen frame is +1, so no orientation or normalization factor remains. -/
theorem coordinateSphereDensity_fluxPullback {k : ℕ}
    (B : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→L[ℝ] ℂ)
    (x : Fin ((2*k+1)+1) → ℝ) :
    MahlerStokes.coordinateSphereDensity 1 (fluxPullback B) x =
      (orientedDensity (sphereFrame k) (sphereVolume k)
        (B (fluxCoordinates k x)).toAlternatingMap (fluxCoordinates k x)).re := by
  classical
  unfold MahlerStokes.coordinateSphereDensity orientedDensity
  rw [sphereVolume_orthonormalFrame, div_one]
  simp only [one_smul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hv : (fluxCoordinates k).toContinuousLinearMap ∘
      i.removeNth (MahlerStokes.coordinateBasis ((2*k+1)+1)) = i.removeNth (sphereFrame k) := by
    funext j
    exact fluxCoordinates_basis k (i.succAbove j)
  simp only [fluxPullback, realFormCLM_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, hv, fluxCoordinates_repr]
  have hs : (-1 : ℂ)^i.val = (((-1 : ℝ)^i.val : ℝ) : ℂ) := by push_cast; rfl
  rw [hs]
  simp only [Complex.mul_re, Complex.mul_im, ContinuousAlternatingMap.coe_toAlternatingMap, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  ring

lemma continuousOn_fluxPullback_sphere {k q : ℕ}
    {B : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin q]→L[ℝ] ℂ}
    (hB : ContinuousOn B (sphere 0 1)) :
    ContinuousOn (fluxPullback B) {x | MahlerStokes.radiusSq x = 1} := by
  apply (realFormCLM _ q).continuous.comp_continuousOn
  apply (ContinuousAlternatingMap.compContinuousLinearMapCLM
    (fluxCoordinates k).toContinuousLinearMap).continuous.comp_continuousOn
  apply hB.comp (fluxCoordinates k).continuous.continuousOn
  intro x hx
  simp only [mem_sphere, dist_zero_right]
  have hh := norm_fluxCoordinates_sq k x
  rw [hx] at hh
  nlinarith [norm_nonneg (fluxCoordinates k x)]

/-- The hemisphere-coordinate Stokes flux is exactly Mahler's real flux of a
complex form. Only continuity on the sphere is required. -/
theorem sphereFlux_eq_coordinateFlux {k : ℕ}
    (B : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→L[ℝ] ℂ)
    (hB : ContinuousOn B (sphere 0 1)) :
    sphereFlux k (fun x => (B x).toAlternatingMap) =
      MahlerStokes.sphereFlux 1 (fluxPullback B) := by
  rw [MahlerStokes.sphereFlux_unit_eq_areaIntegral _ (continuousOn_fluxPullback_sphere hB)]
  let e := (sphereFrame k).repr.symm
  have hm := MahlerStokes.measurePreserving_sphereIsometry e volume volume e.measurePreserving
  have he := hm.integral_comp (MahlerStokes.sphereIsometry e).measurableEmbedding
    (fun z : sphere (0 : ComplexEuclidean (k+1)) 1 =>
      (orientedDensity (sphereFrame k) (sphereVolume k) (B z).toAlternatingMap z).re)
  unfold sphereFlux sphereArea
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with z
  exact (coordinateSphereDensity_fluxPullback B (WithLp.ofLp z.val)).symm

end Mahler

end

end OAI
