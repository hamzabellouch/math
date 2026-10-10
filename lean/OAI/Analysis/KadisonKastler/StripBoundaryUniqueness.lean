import OAI.Analysis.KadisonKastler.HorizontalStripGluing
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.ReImTopology

namespace OAI

/-! # Uniqueness from one boundary of a holomorphic strip -/

namespace KadisonKastler

open Complex Set Filter
open scoped Topology

noncomputable section

private def stripZeroExtension (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then f z else 0

/-- A continuous holomorphic strip is determined by its lower boundary. -/
theorem strip_eq_zero_of_lower_boundary {f : ℂ → ℂ}
    (hc : ContinuousOn f {z | 0 ≤ z.im ∧ z.im ≤ 1})
    (hd : DifferentiableOn ℂ f {z | 0 < z.im ∧ z.im < 1})
    (hzero : ∀ t : ℝ, f t = 0) :
    ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → f z = 0 := by
  let S : Set ℂ := {z | -1 < z.im ∧ z.im < 1}
  have hopen : IsOpen S := isOpen_Ioo.preimage continuous_im
  have hseam {z : ℂ} (hz : z.im = 0) : f z = 0 := by
    have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
    rw [he, hzero]
  have hcont : ContinuousOn (stripZeroExtension f) S := by
    apply ContinuousOn.if
    · intro z hz
      have hz' : z.im = 0 := by
        have hf := hz.2
        change z ∈ frontier (im ⁻¹' Ici (0 : ℝ)) at hf
        rw [frontier_preimage_im, frontier_Ici] at hf
        exact hf
      exact hseam hz'
    · apply hc.mono
      intro z hz
      have hcl : 0 ≤ z.im := by
        have hh : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_Ici.preimage continuous_im
        have hhx := hz.2
        rw [hh.closure_eq] at hhx
        exact hhx
      exact ⟨hcl, hz.1.2.le⟩
    · exact continuousOn_const
  have hdiff : DifferentiableOn ℂ (stripZeroExtension f) S := by
    apply differentiableOn_horizontal_strip_glue (s := 0) (by norm_num) (by norm_num) hcont
    intro z hzlo hzhi hzne
    by_cases hz : 0 < z.im
    · apply (hd.differentiableAt ((isOpen_Ioo.preimage continuous_im).mem_nhds
        ⟨hz, hzhi⟩)).congr_of_eventuallyEq
      filter_upwards [(isOpen_Ioi.preimage continuous_im).mem_nhds hz] with w hw
      exact ite_eq_left hw.le
    · have hneg : z.im < 0 := lt_of_le_of_ne (le_of_not_gt hz) hzne
      apply (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
      filter_upwards [(isOpen_Iio.preimage continuous_im).mem_nhds hneg] with w hw
      exact ite_eq_right (not_le.mpr hw)
  have hconn : IsPreconnected S := by
    exact ((convex_Ioo (-1 : ℝ) 1).linear_preimage imLm).isPreconnected
  have hbase : (-I / 2 : ℂ) ∈ S := by norm_num [S]
  have hevent : stripZeroExtension f =ᶠ[𝓝 (-I / 2 : ℂ)] 0 := by
    filter_upwards [(isOpen_Iio.preimage continuous_im).mem_nhds
      (show (-I / 2 : ℂ).im < 0 by norm_num)] with w hw
    exact ite_eq_right (not_le.mpr hw)
  have hall := (hdiff.analyticOnNhd hopen).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hconn hbase hevent
  have hinner : EqOn f 0 (im ⁻¹' Ioo (0 : ℝ) 1) := by
    intro z hz
    have h := hall (show z ∈ S from ⟨by linarith [hz.1], hz.2⟩)
    simpa only [stripZeroExtension, ite_eq_left hz.1.le] using h
  have hclosure : closure (im ⁻¹' Ioo (0 : ℝ) 1) = {z : ℂ | 0 ≤ z.im ∧ z.im ≤ 1} := by
    rw [closure_preimage_im, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    rfl
  have he := hinner.of_subset_closure hc continuousOn_const
    (fun z hz => ⟨hz.1.le, hz.2.le⟩) (by rw [hclosure])
  intro z hzlo hzhi
  exact he ⟨hzlo, hzhi⟩

theorem strip_eq_of_lower_boundary {f g : ℂ → ℂ}
    (hfc : ContinuousOn f {z | 0 ≤ z.im ∧ z.im ≤ 1})
    (hfd : DifferentiableOn ℂ f {z | 0 < z.im ∧ z.im < 1})
    (hgc : ContinuousOn g {z | 0 ≤ z.im ∧ z.im ≤ 1})
    (hgd : DifferentiableOn ℂ g {z | 0 < z.im ∧ z.im < 1})
    (he : ∀ t : ℝ, f t = g t) :
    ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → f z = g z := by
  have h := strip_eq_zero_of_lower_boundary (hfc.sub hgc) (hfd.sub hgd)
    (fun t => sub_eq_zero.mpr (he t))
  intro z hzlo hzhi
  exact sub_eq_zero.mp (h z hzlo hzhi)

end

end KadisonKastler

end OAI
