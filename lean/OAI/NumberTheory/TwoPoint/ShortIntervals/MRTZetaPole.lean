import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterHighZeros
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

/-! Uniform removal of the zeta pole on a bounded part of the closed right half-plane. -/

namespace TwoPointCorrelations

open Complex Metric Set Filter
open scoped Topology

noncomputable def mrtZetaPoleCorrection (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s - (s - 1)⁻¹

lemma mrt_zeta_pole_correction_continuousAt {s : ℂ}
    (hs : s ≠ 1) (hr : 1 ≤ s.re) :
    ContinuousAt mrtZetaPoleCorrection s := by
  have hd := (analyticOn_riemannZeta s hs).deriv.continuousAt
  have hz := (differentiableAt_riemannZeta hs).continuousAt
  exact (hd.neg.div hz (riemannZeta_ne_zero_of_one_le_re hr)).sub
    ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hs))

/-- After subtracting the pole, the logarithmic derivative is uniformly bounded
on each bounded part of `Re s ≥ 1`, with constants independent of characters. -/
theorem mrt_zeta_pole_correction_bounded (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 ≤ s.re → ‖s‖ ≤ B → s ≠ 1 →
      ‖mrtZetaPoleCorrection s‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := Erdos970.riemannZetaLogDerivResidueBigO.bound
  have he : ∀ᶠ s : ℂ in 𝓝[({1}ᶜ)] 1, ‖mrtZetaPoleCorrection s‖ ≤ C₀ := by
    filter_upwards [hC₀] with s hs
    simpa only [mrtZetaPoleCorrection, Pi.sub_apply, Pi.neg_apply, Pi.div_apply,
      Pi.one_apply, norm_one, mul_one] using hs
  obtain ⟨r, hr, hlocal⟩ := Metric.mem_nhdsWithin_iff.mp he
  let K : Set ℂ := closedBall 0 B ∩ {s : ℂ | 1 ≤ s.re}
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) B).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  have hA : IsCompact (K \ ball (1 : ℂ) r) := hK.diff isOpen_ball
  have hcont : ContinuousOn mrtZetaPoleCorrection (K \ ball (1 : ℂ) r) := by
    intro s hs
    have hn : s ≠ 1 := by
      intro heq
      apply hs.2
      rw [heq]
      exact mem_ball_self hr
    exact (mrt_zeta_pole_correction_continuousAt hn hs.1.2).continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := hA.exists_bound_of_continuousOn hcont
  refine ⟨max 0 (max C₀ C₁), le_max_left _ _, ?_⟩
  intro s hs hn hs1
  by_cases hsr : s ∈ ball (1 : ℂ) r
  · exact (hlocal ⟨hsr, hs1⟩).trans ((le_max_left C₀ C₁).trans (le_max_right _ _))
  · have hm : s ∈ K \ ball (1 : ℂ) r := by
      exact ⟨⟨by simpa only [mem_closedBall, dist_zero_right] using hn, hs⟩, hsr⟩
    exact (hC₁ s hm).trans ((le_max_right C₀ C₁).trans (le_max_right _ _))

lemma mrt_zeta_neg_logderiv_bounded (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 ≤ s.re → ‖s‖ ≤ B → s ≠ 1 →
      (-deriv riemannZeta s / riemannZeta s).re ≤ C + ‖(s - 1)⁻¹‖ := by
  obtain ⟨C, hC, hb⟩ := mrt_zeta_pole_correction_bounded B
  refine ⟨C, hC, ?_⟩
  intro s hs hn hs1
  have h := (Complex.abs_re_le_norm _).trans (hb s hs hn hs1)
  have hi := (le_abs_self ((s - 1)⁻¹).re).trans (Complex.abs_re_le_norm _)
  have hc := (le_abs_self (mrtZetaPoleCorrection s).re).trans h
  dsimp only [mrtZetaPoleCorrection] at hc
  rw [Complex.sub_re] at hc
  linarith

end TwoPointCorrelations

end OAI
