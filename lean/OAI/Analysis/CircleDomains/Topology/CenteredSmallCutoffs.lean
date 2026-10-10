import OAI.Analysis.CircleDomains.Sobolev.SmallEnergyCutoff

namespace OAI

/-! Small-energy smooth cutoffs centered at each actual omitted source
point, with their support inside a prescribed ball. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 def translatedCutoff (f : ℂ → ℝ) (c : ℂ) : ℂ → ℝ := fun z => f (z-c)

 theorem translatedCutoff_fderiv {f : ℂ → ℝ} (hf : Differentiable ℝ f) (c z : ℂ) :
    fderiv ℝ (translatedCutoff f c) z = fderiv ℝ f (z-c) := by
  have hd := (hf (z-c)).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c)
  change fderiv ℝ (fun w : ℂ => f (w-c)) z = _
  simpa only [id_eq, Function.comp_def, ContinuousLinearMap.comp_id] using hd.fderiv

 theorem translatedCutoff_energy {f : ℂ → ℝ} (hf : Differentiable ℝ f) (c : ℂ) :
    (∫ z, ‖fderiv ℝ (translatedCutoff f c) z‖^2) = ∫ z, ‖fderiv ℝ f z‖^2 := by
  simp_rw [translatedCutoff_fderiv hf]
  exact integral_sub_right_eq_self (fun z : ℂ => ‖fderiv ℝ f z‖^2) c

 theorem exists_small_energy_cutoff (c : ℂ) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ ball c R ∧ (∀ z, f z ∈ Icc (0 : ℝ) 1) ∧
      (∀ᶠ z in 𝓝 c, f z = 1) ∧ (∫ z, ‖fderiv ℝ f z‖^2) < ε := by
  obtain ⟨f, hf, hs, hsupport, hunit, hone, henergy⟩ := exists_small_energy_cutoff_zero hR hε
  let g := translatedCutoff f c
  have he : g = f ∘ (Homeomorph.addRight (-c)) := by
    funext z
    change f (z-c) = f (z + -c)
    rw [sub_eq_add_neg]
  refine ⟨g, hf.comp (contDiff_id.sub contDiff_const), ?_, ?_, (fun z => hunit (z-c)), ?_, ?_⟩
  · rw [he]
    exact hs.comp_homeomorph (Homeomorph.addRight (-c))
  · rw [he, tsupport_comp_eq_preimage]
    intro z hz
    change z + -c ∈ tsupport f at hz
    have hh := hsupport hz
    simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_eq_add_neg, neg_zero, add_zero] using hh
  · have ht : Tendsto (fun z : ℂ => z-c) (𝓝 c) (𝓝 0) := by
      simpa only [id_eq, sub_self] using
        (tendsto_id : Tendsto (fun z : ℂ => z) (𝓝 c) (𝓝 c)).sub_const c
    exact ht.eventually hone
  · rw [translatedCutoff_energy (hf.differentiable (by simp))]
    exact henergy

end CircleDomainRigidity

end

end OAI
