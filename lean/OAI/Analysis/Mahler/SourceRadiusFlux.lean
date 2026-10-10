import OAI.Analysis.Mahler.SourceFluxCoordinates
import OAI.Analysis.Mahler.SphereDensityBridge
import OAI.Analysis.Mahler.SphereRadius

namespace OAI

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology
namespace Mahler

lemma continuousOn_sourceFluxForm_sphere {k : ℕ} {u : ComplexEuclidean (k+1) → ℂ}
    {r : ℝ} (hu : ∀ z ∈ sphere (0 : ComplexEuclidean (k+1)) r, ContDiffAt ℝ 3 u z) :
    ContinuousOn (sourceFluxForm u) (sphere 0 r) :=
  fun z hz => (contDiffAt_sourceFluxForm (hu z hz)).continuousAt.continuousWithinAt

/-- Positive dilation of the coordinate integral uses the tangential degree
2k+1, with no change in the outward orientation. -/
theorem sphereFlux_pos_eq_coordinateFlux {k : ℕ} {r : ℝ} (hr : 0 < r)
    (B : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→L[ℝ] ℂ)
    (hB : ContinuousOn B (sphere 0 r)) :
    MahlerStokes.sphereFlux r (fluxPullback B) =
      r^(2*k+1) * sphereFlux k (fun x => (B (r • x)).toAlternatingMap) := by
  rw [MahlerStokes.sphereFlux_pos_scale hr]
  have hc : ContinuousOn (fun x => B (r • x)) (sphere 0 1) := by
    apply hB.comp (by fun_prop) (fun x hx => ?_)
    have hx' : ‖x‖ = 1 := by simpa using hx
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hx']
  rw [sphereFlux_eq_coordinateFlux _ hc]
  congr 1
  congr 1
  funext x
  simp only [fluxPullback, map_smul]

/-- The coordinate Stokes flux equals the real part of the
radius-sphere area integral. C3 is required only at the radius sphere. -/
theorem sourceCoordinateFlux_eq_radiusSphereFlux {k : ℕ}
    {u : ComplexEuclidean (k+1) → ℂ} {r : ℝ} (hr : 0 < r)
    (hu : ∀ z ∈ sphere (0 : ComplexEuclidean (k+1)) r, ContDiffAt ℝ 3 u z) :
    MahlerStokes.sphereFlux r (sourceCoordinateForm (sourceCoordinates k) u k) =
      (radiusSphereFlux k u r).re := by
  rw [sourceCoordinateForm_eq_fluxPullback,
    sphereFlux_pos_eq_coordinateFlux hr _ (continuousOn_sourceFluxForm_sphere hu)]
  simp only [sourceFluxForm_toAlternatingMap]
  have hu2 : ∀ z : sphere (0 : ComplexEuclidean (k+1)) r,
      ContDiffAt ℝ 2 u (z : ComplexEuclidean (k+1)) :=
    fun z => (hu z z.property).of_le (by norm_num)
  have hsmall := radiusSphereFlux_eq_small (k := k) (u := u) r hr hu2
  conv_rhs => rw [hsmall]
  let : IsFiniteMeasure (sphereArea (k+1)) := by unfold sphereArea; infer_instance
  let : CompactSpace (sphere (0 : ComplexEuclidean (k+1)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hc : Continuous (fun z : sphere (0 : ComplexEuclidean (k+1)) 1 =>
      sphereDensity k z (boundaryForm u k (r • (z : ComplexEuclidean (k+1))))) := by
    convert (continuous_radiusFluxDensity (k := k) (u := u) r hu2).comp
      (continuous_sphereDilation (n := k+1) r hr) using 1
    funext z
    simp [sphereDilation, smul_smul, hr.ne']
  have hi : Integrable (fun z : sphere (0 : ComplexEuclidean (k+1)) 1 =>
      sphereDensity k z (boundaryForm u k (r • (z : ComplexEuclidean (k+1)))))
      (sphereArea (k+1)) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold smallSphereFlux
  rw [integral_const_mul]
  have hp : (r : ℂ)^(2*k+1) = ((r^(2*k+1) : ℝ) : ℂ) := by simp
  rw [hp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  have hre := integral_re hi
  simp only [RCLike.re_eq_complex_re] at hre
  rw [← hre]
  unfold sphereFlux
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : ‖(z : ComplexEuclidean (k+1))‖ = 1 := by simp
  exact congrArg Complex.re (sphereDensity_eq_orientedDensity hz
    (boundaryForm u k (r • (z : ComplexEuclidean (k+1))))).symm

/-- The mass hypotheses supply every regularity premise. Only the
positive radius and inclusion of its sphere in the source domain remain. -/
theorem MassHypotheses.sourceCoordinateFlux_eq_radiusSphereFlux {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G)
    {r : ℝ} (hr : 0 < r) (hSU : sphere (0 : ComplexEuclidean (k+1)) r ⊆ U) :
    MahlerStokes.sphereFlux r (sourceCoordinateForm (sourceCoordinates k) (logTau f) k) =
      (radiusSphereFlux k (logTau f) r).re := by
  apply Mahler.sourceCoordinateFlux_eq_radiusSphereFlux hr
  intro z hz
  apply h.contDiffAt_logTau (hSU hz) _ 3
  intro he
  have hn : ‖z‖ = r := by simpa using hz
  simp [he] at hn
  linarith

/-- The coordinate small-sphere limit, with no flux-bridge premise. -/
theorem MassHypotheses.sourceCoordinateFlux_limit {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    Tendsto (fun r => MahlerStokes.sphereFlux r
      (sourceCoordinateForm (sourceCoordinates k) (logTau f) k))
      (𝓝[>] 0) (𝓝 (homogeneousSphereFlux k N G)) := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp h.open_domain 0 h.zero_mem
  apply h.small_sphere_real_flux_limit.congr'
  filter_upwards [self_mem_nhdsWithin, (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ) : Iio δ ∈ 𝓝[>] (0 : ℝ))] with r hr hrδ
  symm
  apply h.sourceCoordinateFlux_eq_radiusSphereFlux hr
  intro z hz
  apply hδU
  have hn : ‖z‖ = r := by simpa using hz
  simpa [mem_ball, dist_zero_right, hn] using hrδ

end Mahler

end

end OAI
