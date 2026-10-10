import OAI.Analysis.Mahler.LogDilation

namespace OAI

open Complex MeasureTheory Metric Filter Set
open scoped Topology

namespace Mahler

/-- A fixed closed annulus about the unit sphere. -/
def sphereAnnulus (n : ℕ) : Set (ComplexEuclidean n) :=
  closedBall 0 2 ∩ {z | (1/2 : ℝ) ≤ ‖z‖}

lemma isCompact_sphereAnnulus (n : ℕ) : IsCompact (sphereAnnulus n) :=
  (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)

lemma sphere_subset_annulus (n : ℕ) : sphere (0 : ComplexEuclidean n) 1 ⊆ sphereAnnulus n := by
  intro z hz
  have hn : ‖z‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hz
  constructor <;> norm_num [mem_closedBall, dist_zero_right, hn]

lemma sphereAnnulus_ne_zero {n : ℕ} {z : ComplexEuclidean n} (hz : z ∈ sphereAnnulus n) : z ≠ 0 := by
  intro he
  have := hz.2
  norm_num [he] at this

/-- All regularity and positivity for small rescaled points follows from the
literal open-domain and isolated-zero hypotheses. -/
theorem MassHypotheses.eventually_sphereAnnulus_log_regular {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z ∈ sphereAnnulus (k+1),
      ContinuousAt (tau f) (r • z) ∧ 0 < tau f (r • z) ∧
      ContDiffAt ℝ 2 (logTau f) (r • z) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp h.open_domain 0 h.zero_mem
  have hd : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < δ/3 :=
    (eventually_lt_nhds (by linarith : (0 : ℝ) < δ/3)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hd] with r hr hdr
  intro z hz
  have hz2 : ‖z‖ ≤ 2 := by simpa [mem_closedBall, dist_zero_right] using hz.1
  have hmem : r • z ∈ U := by
    apply hball
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hr0 : 0 < r := hr
    nlinarith [mul_nonneg hr0.le (sub_nonneg.mpr hz2)]
  have hnz : r • z ≠ 0 := smul_ne_zero hr.ne' (sphereAnnulus_ne_zero hz)
  have hp : 0 < tau f (r • z) := by
    apply tau_pos_of_component_ne_zero
    by_contra he
    push Not at he
    exact hnz ((h.isolated_zero _ hmem).mp he)
  have hf := fun j => (h.holomorphic j (r • z) hmem).differentiableAt (h.open_domain.mem_nhds hmem)
  have hc : ContinuousAt (tau f) (r • z) := by
    have hc := Complex.continuous_re.continuousAt.comp (differentiable_energy hf).continuousAt
    simpa only [Function.comp_def, energy_eq_tau, Complex.ofReal_re] using hc
  exact ⟨hc, hp, contDiffAt_logTau_of_open h.open_domain hmem h.holomorphic hp⟩

/-- C^2 regularity of the actual rescaled logarithm; no regularity premise is
added to MassHypotheses. -/
theorem MassHypotheses.eventually_rescaledLog_C2 {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z ∈ sphereAnnulus (k+1),
      ContDiffAt ℝ 2 (rescaledLog (tau f) m r) z := by
  filter_upwards [self_mem_nhdsWithin, h.eventually_sphereAnnulus_log_regular] with r hr hreg
  intro z hz
  obtain ⟨hc, hp, hl⟩ := hreg z hz
  have he := rescaledLog_eventually m hr hc hp
  have hs : ContDiffAt ℝ 2 (fun y => logTau f (r • y) - ((2*m : ℕ) : ℂ) * (Real.log r : ℂ)) z :=
    (hl.comp z (realDilation r).contDiff.contDiffAt).sub contDiffAt_const
  exact hs.congr_of_eventuallyEq he

theorem MassHypotheses.actual_small_sphere_limit {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G)
    (h1 : TendstoUniformlyOn (fun r => fderiv ℝ (rescaledLog (tau f) m r))
      (fderiv ℝ (logTau (polynomialMap G))) (𝓝[>] 0) (sphereAnnulus (k+1)))
    (h2 : TendstoUniformlyOn (fun r => fderiv ℝ (fderiv ℝ (rescaledLog (tau f) m r)))
      (fderiv ℝ (fderiv ℝ (logTau (polynomialMap G)))) (𝓝[>] 0) (sphereAnnulus (k+1))) :
    Tendsto (smallSphereFlux k (logTau f)) (𝓝[>] 0)
      (𝓝 (unitSphereFlux k (logTau (polynomialMap G)))) := by
  have hg : ∀ z ∈ sphereAnnulus (k+1), ContDiffAt ℝ 2 (logTau (polynomialMap G)) z := by
    intro z hz
    apply contDiffAt_logTau_of_open isOpen_univ (mem_univ z)
      (fun j => (polynomialMap_differentiable G j).differentiableOn)
    exact tau_pos_of_component_ne_zero (h.leading_nonzero z (sphereAnnulus_ne_zero hz))
  have hc := h.eventually_sphereAnnulus_log_regular
  apply smallSphereFlux_log_tendsto (isCompact_sphereAnnulus (k+1)) (sphere_subset_annulus (k+1))
    hg h.eventually_rescaledLog_C2
  · exact hc.mono (fun r hr z => (hr z (sphere_subset_annulus _ z.property)).1)
  · exact hc.mono (fun r hr z => (hr z (sphere_subset_annulus _ z.property)).2.1)
  · exact hc.mono (fun r hr z => (hr z (sphere_subset_annulus _ z.property)).2.2)
  · exact h1
  · exact h2

end Mahler

end OAI
