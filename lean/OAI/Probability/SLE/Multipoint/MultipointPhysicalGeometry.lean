import OAI.Probability.SLE.Multipoint.MultipointGeometry

namespace OAI

/-! Disk uniformizations of the actual surviving physical domains.
The radius includes the derivative of the original conformal map, with
no uniform bound on that derivative. -/

noncomputable section
open Set Metric Filter
open scoped Topology NNReal

namespace SLEExactGauge

def physicalConformalRadius (J : ℂ → ℂ) (G : ℝ≥0 → ℂ → ℂ)
    (t : ℝ≥0) (z : ℂ) : ℝ := ‖deriv J z‖ * fullRadius G t z

def physicalDiskChart (J : ℂ → ℂ) (F G : ℝ≥0 → ℂ → ℂ)
    (t : ℝ≥0) (z : ℂ) : ℂ → ℂ := J ∘ F t ∘ diskToHalfPlane (G t z)

theorem IsCapacityTwoWitness.physical_disk_chart
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F)
    (J : ℂ → ℂ) (hJ : DifferentiableOn ℂ J upperHalfPlane)
    (hJinj : InjOn J upperHalfPlane)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t) :
    DifferentiableOn ℂ (physicalDiskChart J F G t z) (ball 0 1) ∧
      InjOn (physicalDiskChart J F G t z) (ball 0 1) ∧
      physicalDiskChart J F G t z 0 = J z ∧
      ‖deriv (physicalDiskChart J F G t z) 0‖ = physicalConformalRadius J G t z ∧
      ∀ w ∈ survivingDomain γ t,
        physicalDiskChart J F G t z (halfPlaneToDisk (G t z) (G t w)) = J w := by
  have hγ := h.1
  rcases h with ⟨_, _, _, hG, hF, hGmap, hFmap, hinv, hinv', _, _, _, _⟩
  have hy : 0 < (G t z).im := hGmap t hz
  let f : ℂ → ℂ := F t ∘ diskToHalfPlane (G t z)
  have hfd : DifferentiableOn ℂ f (ball 0 1) :=
    (hF t).comp (diskToHalfPlane_differentiable _) (diskToHalfPlane_maps hy)
  have hfmap : MapsTo f (ball 0 1) upperHalfPlane := by
    intro v hv
    exact (hFmap t (diskToHalfPlane_maps hy hv)).1.1
  have hfi : InjOn f (ball 0 1) := by
    intro v hv w hw he
    apply diskToHalfPlane_injOn hy hv hw
    have he' := congrArg (G t) he
    change G t (F t (diskToHalfPlane (G t z) v)) =
      G t (F t (diskToHalfPlane (G t z) w)) at he'
    rwa [hinv' t _ (diskToHalfPlane_maps hy hv),
      hinv' t _ (diskToHalfPlane_maps hy hw)] at he'
  have hf0 : f 0 = z := by simp only [f, Function.comp_apply, diskToHalfPlane_zero, hinv t z hz]
  have hdG := ((hG t).differentiableAt ((isOpen_survivingDomain hγ t).mem_nhds hz)).hasDerivAt
  have hdF := ((hF t).differentiableAt (isOpen_upperHalfPlane.mem_nhds (hGmap t hz))).hasDerivAt
  have hident : (fun v => F t (G t v)) =ᶠ[𝓝 z] (fun v => v) := by
    filter_upwards [(isOpen_survivingDomain hγ t).mem_nhds hz] with v hv
    exact hinv t v hv
  have hprod : deriv (F t) (G t z) * deriv (G t) z = 1 :=
    ((hdF.comp z hdG).congr_of_eventuallyEq hident.symm).unique (hasDerivAt_id z)
  have hnormprod : ‖deriv (F t) (G t z)‖ * ‖deriv (G t) z‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm hprod
  have hgn : ‖deriv (G t) z‖ ≠ 0 := by
    intro he
    rw [he, mul_zero] at hnormprod
    norm_num at hnormprod
  have hdF' : HasDerivAt (F t) (deriv (F t) (G t z)) (diskToHalfPlane (G t z) 0) := by
    simpa only [diskToHalfPlane_zero] using hdF
  have hdf : HasDerivAt f (deriv (F t) (G t z) * (G t z-star (G t z))) 0 :=
    hdF'.comp 0 (diskToHalfPlane_deriv_zero _)
  have hfrad : ‖deriv f 0‖ = fullRadius G t z := by
    rw [hdf.deriv, norm_mul, norm_sub_conj_of_im_pos hy, fullRadius]
    apply (eq_div_iff hgn).mpr
    nlinarith [hnormprod]
  have hdJ := (hJ.differentiableAt (isOpen_upperHalfPlane.mem_nhds hz.1.1)).hasDerivAt
  have hdcomp : HasDerivAt (J ∘ f) (deriv J z * deriv f 0) 0 := by
    have hdJ' : HasDerivAt J (deriv J z) (f 0) := by rwa [hf0]
    have hh := hdJ'.comp 0 hdf
    simpa only [hdf.deriv] using hh
  refine ⟨hJ.comp hfd hfmap, hJinj.comp hfi hfmap, ?_, ?_, ?_⟩
  · exact congrArg J hf0
  · change ‖deriv (J ∘ f) 0‖ = _
    rw [hdcomp.deriv, norm_mul, hfrad]
    rfl
  · intro w hw
    dsimp only [physicalDiskChart, Function.comp_apply]
    rw [diskToHalfPlane_halfPlaneToDisk hy (hGmap t hw), hinv t w hw]

theorem IsCapacityTwoWitness.physical_interaction_decay
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F)
    (hgrowth : PublishedDiskUnivalentGrowth)
    (J : ℂ → ℂ) (hJ : DifferentiableOn ℂ J upperHalfPlane)
    (hJinj : InjOn J upperHalfPlane)
    (t : ℝ≥0) (z w : ℂ) (hz : z ∈ survivingDomain γ t)
    (hw : w ∈ survivingDomain γ t) (hne : z ≠ w)
    (b a u : ℝ) (hb : b ≤ dist (J z) (J w))
    (hR : physicalConformalRadius J G t z = b*Real.exp (-2*a*u)) :
    halfPlaneGreen (G t z) (G t w) ≤ Real.exp (-a*u) := by
  obtain ⟨hfd, hfi, hf0, hfrad, hfpoint⟩ := h.physical_disk_chart J hJ hJinj t z hz
  let ξ := halfPlaneToDisk (G t z) (G t w)
  have hξ : ξ ∈ ball (0 : ℂ) 1 :=
    halfPlaneToDisk_maps (h.imag_positive t z hz) (h.imag_positive t w hw)
  have hξ0 : ξ ≠ 0 := by
    intro he
    have hv := hfpoint w hw
    change physicalDiskChart J F G t z ξ = J w at hv
    rw [he, hf0] at hv
    exact hne (hJinj hz.1.1 hw.1.1 hv)
  rw [halfPlaneGreen_eq_disk]
  apply Multipoint.disk_interaction_decay hgrowth _ hfd hfi ξ hξ hξ0 b a u
  · rw [hfpoint w hw, hf0, norm_sub_rev, ← dist_eq_norm]
    exact hb
  · exact hfrad.trans hR

end SLEExactGauge

end

end OAI
