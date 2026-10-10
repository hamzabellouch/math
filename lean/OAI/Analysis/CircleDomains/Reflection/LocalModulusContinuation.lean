import OAI.Analysis.CircleDomains.Reflection.ModulusBoundaryContinuation

namespace OAI

/-! The lower modulus bound in the logarithm argument is automatic
locally from the actual boundary trace. -/
open Set Function Filter Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_local_holomorphic_continuation_of_modulus_trace {R : ℝ} {f : ℂ → ℂ}
    (hR : 0<R) (hd : DifferentiableOn ℂ f (upperSemidisk R))
    (hupper : ∀z∈upperSemidisk R,‖f z‖<1)
    (htrace : ∀p:ℂ,‖p‖≤R → p.im=0 →
      Tendsto (fun z => ‖f z‖) (𝓝[upperSemidisk R] p) (𝓝 1)) :
    ∃ (V : Set ℂ) (F : ℂ → ℂ), IsOpen V ∧ (0:ℂ)∈V ∧ V⊆ball 0 R ∧
      DifferentiableOn ℂ F V ∧ EqOn F f (V∩{z : ℂ | 0<z.im}) := by
  have ht := htrace 0 (by simpa using hR.le) (by simp)
  have he : ∀ᶠ z in 𝓝[upperSemidisk R] (0:ℂ),(1/2:ℝ)<‖f z‖ :=
    ht.eventually (eventually_gt_nhds (by norm_num : (1/2:ℝ)<1))
  obtain ⟨δ,hδ,hδbound⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp he)
  let r := min R δ/2
  have hr : 0<r := by dsimp [r];positivity
  have hrR : r≤R := by dsimp [r];nlinarith [min_le_left R δ]
  have hrδ : r<δ := by dsimp [r];nlinarith [min_le_right R δ]
  have hlower : ∀z∈upperSemidisk r,(1/2:ℝ)≤‖f z‖ := by
    intro z hz
    apply le_of_lt
    apply hδbound
    · simpa only [dist_zero_right] using (mem_ball_zero_iff.mp hz.1).trans hrδ
    · exact upperSemidisk_mono hrR hz
  have htr : ∀p:ℂ,‖p‖≤r → p.im=0 →
      Tendsto (fun z => ‖f z‖) (𝓝[upperSemidisk r] p) (𝓝 1) := by
    intro p hp hp0
    exact (htrace p (hp.trans hrR) hp0).mono_left
      (nhdsWithin_mono p (upperSemidisk_mono hrR))
  obtain ⟨V,F,hV,h0,hVr,hFd,hFe⟩ := exists_holomorphic_continuation_of_modulus_trace
    hr (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤1)
    (hd.mono (upperSemidisk_mono hrR)) hlower
    (fun z hz => hupper z (upperSemidisk_mono hrR hz)) htr
  exact ⟨V,F,hV,h0,hVr.trans (ball_subset_ball (by linarith)),hFd,hFe⟩

end CircleDomainRigidity

end

end OAI
