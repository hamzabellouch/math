import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.QuantitativeFlatAnnularAlternative

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem HasFlatBallAbove.to_physical {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s ρ cap ε : ℝ) (hs : 0 < s)
    (hflat : HasFlatBallAbove n (blowupMeasure n μ a s) (ball 0 cap) ρ cap ε) :
    HasFlatBallAbove n μ (ball a (s * cap)) (s * ρ) (s * cap) ε := by
  obtain ⟨b, hb, hbU, r, hr, hρr, hrcap, hbeta⟩ := hflat
  refine ⟨a + s • b, (blowupMeasure_support_iff n μ a b s hs).mp hb, ?_,
    s * r, mul_pos hs hr, mul_le_mul_of_nonneg_left hρr hs.le,
    mul_lt_mul_of_pos_left hrcap hs, ?_⟩
  · change dist (a + s • b) a < s * cap
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    apply mul_lt_mul_of_pos_left _ hs
    simpa only [mem_ball, dist_zero_right] using! hbU
  · rwa [← bilateralBeta_blowup_at n μ a b s r hs]

theorem HasLargeSmoothAnnulusAbove.to_physical {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s ρ cap B : ℝ) (hs : 0 < s)
    (hann : HasLargeSmoothAnnulusAbove n (blowupMeasure n μ a s) (ball 0 cap) ρ cap B) :
    HasLargeSmoothAnnulusAbove n μ (ball a (s * cap)) (s * ρ) (s * cap) B := by
  obtain ⟨b, hb, hbU, r, R, hr, hrR, hρr, hRcap, hnorm⟩ := hann
  refine ⟨a + s • b, (blowupMeasure_support_iff n μ a b s hs).mp hb, ?_,
    s * r, s * R, mul_pos hs hr, mul_le_mul_of_nonneg_left hrR hs.le,
    mul_le_mul_of_nonneg_left hρr hs.le, mul_lt_mul_of_pos_left hRcap hs, ?_⟩
  · change dist (a + s • b) a < s * cap
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    apply mul_lt_mul_of_pos_left _ hs
    simpa only [mem_ball, dist_zero_right] using! hbU
  · rwa [smoothAnnularTransform_blowup n μ a b s r R hs hr (hr.trans_le hrR)] at hnorm

theorem exists_uniform_physical_flat_annular_radius {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (C G B ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 16 ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth n G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) →
      ∀ a ∈ μ.support, ∀ s : ℝ, 0 < s → AdmissibleRadius μ (s / 8) →
      HasFlatBallAbove n μ (ball a (s / 16)) (ρ * s) (s / 16) ε ∨
        HasLargeSmoothAnnulusAbove n μ (ball a (s / 16)) (ρ * s) (s / 16) B := by
  obtain ⟨ρ, hρ, hρcap, hchoose⟩ := exists_uniform_flat_annular_radius hn hnd C G (1 / 8) B (1 / 16) ε
    hC (by norm_num) (by norm_num) hε (ball (0 : Ambient d) (1 / 16)) isOpen_ball
    (mem_ball_self (by norm_num))
  refine ⟨ρ, hρ, hρcap, ?_⟩
  intro μ hg hlower a ha s hs hcore
  have hl : CappedLowerGrowth n C (s / 8) μ := by
    intro x hx r hr hrs
    exact hlower x hx r ⟨hr, (ENNReal.ofReal_le_ofReal hrs).trans hcore.2⟩
  have hlscaled : CappedLowerGrowth n C (1 / 8) (blowupMeasure n μ a s) := by
    have ht := CappedLowerGrowth.blowup n C (s / 8) μ hl a s hs
    have heq : (s / 8) / s = (1 / 8 : ℝ) := by field_simp
    simpa only [heq] using! ht
  rcases hchoose (blowupMeasure n μ a s) (blowupMeasure_growth n μ a s G hs hg) hlscaled
    (blowupMeasure_origin_mem_support n μ a s hs ha) with hflat | hann
  · left
    simpa only [mul_one_div, mul_comm s ρ] using! HasFlatBallAbove.to_physical n μ a s ρ (1 / 16) ε hs hflat
  · right
    simpa only [mul_one_div, mul_comm s ρ] using!
      HasLargeSmoothAnnulusAbove.to_physical n μ a s ρ (1 / 16) B hs hann

end

end RieszRectifiability

end OAI
