import OAI.Analysis.CircleDomains.Transfer.RegularC1Chart

namespace OAI

/-! Regular scalar coordinates with both ambient spaces represented by ℂ. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma exists_complex_c1_level_chart {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) {z : ℂ} (hzD : z ∈ D)
    (hz : fderiv ℝ f z ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, z ∈ e.source ∧ e.source ⊆ D ∧
      (∀ w, (e w).re = f w) ∧ ContDiffOn ℝ 1 e e.source ∧
      ContDiffOn ℝ 1 e.symm e.target := by
  obtain ⟨e, hz, heD, he, heC, hiC⟩ := exists_c1_planar_level_chart hD hf hzD hz
  let g := e.transHomeomorph Complex.equivRealProdCLM.symm.toHomeomorph
  refine ⟨g, hz, heD, ?_, ?_, ?_⟩
  · intro w
    exact he w
  · change ContDiffOn ℝ 1 (Complex.equivRealProdCLM.symm ∘ e) e.source
    exact Complex.equivRealProdCLM.symm.contDiff.comp_contDiffOn heC
  · change ContDiffOn ℝ 1 (e.symm ∘ Complex.equivRealProdCLM) g.target
    apply hiC.comp Complex.equivRealProdCLM.contDiff.contDiffOn
    intro y hy
    exact hy

end CircleDomainRigidity

end

end OAI
