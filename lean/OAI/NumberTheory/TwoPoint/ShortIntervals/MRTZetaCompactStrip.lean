import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTZetaPole

namespace OAI

/-! A fixed bounded-height strip for the pole-corrected zeta logarithmic
derivative, from zero-free compactness. -/

namespace TwoPointCorrelations

open Complex Metric Set Filter
open scoped Topology

theorem mrt_zeta_compact_strip (B : ℝ) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ 0 ≤ C ∧ ∀ s : ℂ,
      1 - a ≤ s.re → ‖s‖ ≤ B → s ≠ 1 →
        riemannZeta s ≠ 0 ∧ ‖mrtZetaPoleCorrection s‖ ≤ C := by
  let U := |B| + 1
  obtain ⟨σ₀, hσ₀, hz⟩ := Erdos970.ZetaNoZerosInBox U
  let A := max σ₀ (1 / 2)
  have hA : A < 1 := max_lt hσ₀ (by norm_num)
  have hAh : 1 / 2 ≤ A := le_max_right _ _
  have hnon (s : ℂ) (hs : A ≤ s.re) (hn : ‖s‖ ≤ U) : riemannZeta s ≠ 0 := by
    have hi := (Complex.abs_im_le_norm s).trans hn
    have hh := hz s.im hi s.re ((le_max_left _ _).trans hs)
    simpa only [Complex.re_add_im] using hh
  obtain ⟨C₀, hC₀⟩ := Erdos970.riemannZetaLogDerivResidueBigO.bound
  have he : ∀ᶠ s : ℂ in 𝓝[({1}ᶜ)] 1, ‖mrtZetaPoleCorrection s‖ ≤ C₀ := by
    filter_upwards [hC₀] with s hs
    simpa only [mrtZetaPoleCorrection, Pi.sub_apply, Pi.neg_apply, Pi.div_apply,
      Pi.one_apply, norm_one, mul_one] using hs
  obtain ⟨r, hr, hlocal⟩ := Metric.mem_nhdsWithin_iff.mp he
  let K : Set ℂ := closedBall 0 U ∩ {s : ℂ | A ≤ s.re}
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) U).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  have hE : IsCompact (K \ ball (1 : ℂ) r) := hK.diff isOpen_ball
  have hcont : ContinuousOn mrtZetaPoleCorrection (K \ ball (1 : ℂ) r) := by
    intro s hs
    have hs1 : s ≠ 1 := by
      intro heq
      apply hs.2
      rw [heq]
      exact mem_ball_self hr
    have hn : riemannZeta s ≠ 0 := hnon s hs.1.2 (by simpa using hs.1.1)
    have hd := (analyticOn_riemannZeta s hs1).deriv.continuousAt
    have hc := (differentiableAt_riemannZeta hs1).continuousAt
    exact ((hd.neg.div hc hn).sub
      ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hs1))).continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := hE.exists_bound_of_continuousOn hcont
  refine ⟨1 - A, max 0 (max C₀ C₁), by linarith, by linarith, le_max_left _ _, ?_⟩
  intro s hs hn hs1
  have hsA : A ≤ s.re := by linarith
  have hnU : ‖s‖ ≤ U := hn.trans (by dsimp [U]; linarith [le_abs_self B])
  refine ⟨hnon s hsA hnU, ?_⟩
  by_cases hsr : s ∈ ball (1 : ℂ) r
  · exact (hlocal ⟨hsr, hs1⟩).trans ((le_max_left C₀ C₁).trans (le_max_right _ _))
  · have hm : s ∈ K \ ball (1 : ℂ) r := by
      exact ⟨⟨by simpa only [mem_closedBall, dist_zero_right] using hnU, hsA⟩, hsr⟩
    exact (hC₁ s hm).trans ((le_max_right C₀ C₁).trans (le_max_right _ _))

end TwoPointCorrelations

end OAI
