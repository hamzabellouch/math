import OAI.Analysis.Mahler.SourceSphereLimit
import OAI.Analysis.Mahler.SourceLogC2

namespace OAI

open Complex Filter Set
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def complexifyDerivative : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℂ) :=
  ContinuousLinearMap.compL ℝ E ℝ ℂ Complex.ofRealCLM
noncomputable def complexifySecondDerivative :
    (E →L[ℝ] (E →L[ℝ] ℝ)) →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℂ)) :=
  ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) (E →L[ℝ] ℂ) complexifyDerivative

lemma fderiv_ofReal_eq {u : E → ℝ} {x : E} (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun y => (u y : ℂ)) x = complexifyDerivative (fderiv ℝ u x) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x hu.hasFDerivAt
  exact hd.fderiv

lemma fderiv_twice_ofReal_eq {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    fderiv ℝ (fderiv ℝ (fun y => (u y : ℂ))) x =
      complexifySecondDerivative (fderiv ℝ (fderiv ℝ u) x) := by
  have he : fderiv ℝ (fun y => (u y : ℂ)) =ᶠ[𝓝 x]
      (fun y => complexifyDerivative (fderiv ℝ u y)) := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    exact fderiv_ofReal_eq (hy.differentiableAt (by norm_num))
  have hd := complexifyDerivative.hasFDerivAt.comp x
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  rw [he.fderiv_eq]
  exact hd.fderiv

/-- Scalar extension from real log jets to complex-valued real differential forms. -/
theorem uniform_log_jets_ofReal [FiniteDimensional ℝ E]
    {I : Type*} {l : Filter I} {u : I → E → ℝ} {v : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hv : ∀ x ∈ K, ContDiffAt ℝ 2 v x)
    (hu : ∀ᶠ i in l, ∀ x ∈ K, ContDiffAt ℝ 2 (u i) x)
    (h1 : TendstoUniformlyOn (fun i => fderiv ℝ (u i)) (fderiv ℝ v) l K)
    (h2 : TendstoUniformlyOn (fun i => fderiv ℝ (fderiv ℝ (u i))) (fderiv ℝ (fderiv ℝ v)) l K) :
    TendstoUniformlyOn (fun i => fderiv ℝ (fun x => (u i x : ℂ)))
      (fderiv ℝ (fun x => (v x : ℂ))) l K ∧
    TendstoUniformlyOn (fun i => fderiv ℝ (fderiv ℝ (fun x => (u i x : ℂ))))
      (fderiv ℝ (fderiv ℝ (fun x => (v x : ℂ)))) l K := by
  have hc1 : ContinuousOn (fderiv ℝ v) K := by
    intro x hx
    exact ((hv x hx).fderiv_right (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  have hc2 : ContinuousOn (fderiv ℝ (fderiv ℝ v)) K := by
    intro x hx
    exact (((hv x hx).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
      (by norm_num)).continuousAt.continuousWithinAt
  have h1' := SymmetricMahler.uniform_comp_of_compact hK hc1 h1 complexifyDerivative.continuous
  have h2' := SymmetricMahler.uniform_comp_of_compact
    (E := E →L[ℝ] (E →L[ℝ] ℝ)) (H := E →L[ℝ] (E →L[ℝ] ℂ))
    hK hc2 h2 (complexifySecondDerivative (E := E)).continuous
  constructor
  · apply (h1'.congr_right (fun x hx => (fderiv_ofReal_eq
      ((hv x hx).differentiableAt (by norm_num))).symm)).congr
    filter_upwards [hu] with i hi
    intro x hx
    exact (fderiv_ofReal_eq ((hi x hx).differentiableAt (by norm_num))).symm
  · apply (h2'.congr_right (fun x hx => (fderiv_twice_ofReal_eq (hv x hx)).symm)).congr
    filter_upwards [hu] with i hi
    intro x hx
    exact (fderiv_twice_ofReal_eq (hi x hx)).symm

lemma sphereAnnulus_eq_logCompactAnnulus (n : ℕ) :
    sphereAnnulus n = SymmetricMahler.logCompactAnnulus n := by
  ext z
  simp [sphereAnnulus, SymmetricMahler.logCompactAnnulus, Metric.mem_ball, dist_zero_right]

theorem MassHypotheses.small_sphere_flux_limit {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    Tendsto (smallSphereFlux k (logTau f)) (𝓝[>] 0)
      (𝓝 (unitSphereFlux k (logTau (polynomialMap G)))) := by
  let u := MahlerRescaling.rescaledLogEnergy f m
  let v := MahlerRescaling.leadingLogEnergy G
  have eu (r : ℝ) : (fun x => (u r x : ℂ)) = rescaledLog (tau f) m r := by
    funext x
    rw [show u r x = Real.log ((r^(2*m))⁻¹ * tau f (r • x)) from
      MahlerRescaling.rescaledLogEnergy_eq_log_tau r x]
    rfl
  have ev : (fun x => (v x : ℂ)) = logTau (polynomialMap G) := rfl
  have hvC : ∀ x ∈ sphereAnnulus (k+1), ContDiffAt ℝ 2 (logTau (polynomialMap G)) x := by
    intro x hx
    exact contDiffAt_logTau_of_open isOpen_univ (mem_univ x)
      (fun j => (polynomialMap_differentiable G j).differentiableOn)
      (tau_pos_of_component_ne_zero (h.leading_nonzero x (sphereAnnulus_ne_zero hx)))
  have hvR : ∀ x ∈ sphereAnnulus (k+1), ContDiffAt ℝ 2 v x := by
    intro x hx
    have hc := Complex.reCLM.contDiff.contDiffAt.comp x (hvC x hx)
    change ContDiffAt ℝ 2 (fun y => (logTau (polynomialMap G) y).re) x at hc
    simpa only [← ev, Complex.ofReal_re] using hc
  have huR : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ x ∈ sphereAnnulus (k+1), ContDiffAt ℝ 2 (u r) x := by
    filter_upwards [h.eventually_rescaledLog_C2] with r hr
    intro x hx
    have hc := Complex.reCLM.contDiff.contDiffAt.comp x (hr x hx)
    change ContDiffAt ℝ 2 (fun y => (rescaledLog (tau f) m r y).re) x at hc
    simpa only [← eu r, Complex.ofReal_re] using hc
  obtain ⟨_, _, h1, h2⟩ := MahlerRescaling.source_rescaling_log_uniform_C2 h
  rw [← sphereAnnulus_eq_logCompactAnnulus] at h1 h2
  obtain ⟨hc1, hc2⟩ := uniform_log_jets_ofReal (isCompact_sphereAnnulus (k+1)) hvR huR h1 h2
  simp only [eu, ev] at hc1 hc2
  exact h.actual_small_sphere_limit hc1 hc2

end Mahler

end OAI
