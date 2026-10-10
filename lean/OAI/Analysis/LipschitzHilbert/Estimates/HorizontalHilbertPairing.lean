import OAI.Analysis.LipschitzHilbert.Estimates.HorizontalHilbertLp
import OAI.Analysis.LipschitzHilbert.Fourier.ActualCutoffBandHigh

namespace OAI

/-! Restricted horizontal estimates at the two exponents used in the
manuscript, transferred to the original vertical cutoff. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem schwartz_power_le_l1 (f : SchwartzMap (ℝ×ℝ) ℂ)
    (hf : ∀ z, ‖f z‖≤1) (p : ℝ) (hp : 1≤p) :
    (∫ z, ‖f z‖^p ∂planeMeasure)≤∫ z, ‖f z‖ ∂planeMeasure := by
  have hp0 : 0<p := lt_of_lt_of_le zero_lt_one hp
  have hi : Integrable (fun z => ‖f z‖^p) planeMeasure := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      (f.memLp (ENNReal.ofReal p) planeMeasure).integrable_norm_rpow
        (by simpa only [ne_eq,ENNReal.ofReal_eq_zero,not_le] using hp0) (by simp)
  exact integral_mono hi (f.integrable.norm) fun z =>
    Real.rpow_le_self_of_le_one (norm_nonneg _) (hf z) hp

theorem horizontalHilbert_restricted_pairing (hH : HorizontalHilbertInput) :
    ∃ C : ℝ, 0<C ∧ ∀ p q : ℝ, (p=3/2 ∨ p=4) → p.HolderConjugate q →
      ∀ r R : ℝ, 0<r → r≤R → ∀ f g : SchwartzMap (ℝ×ℝ) ℂ,
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      ‖∫ z, horizontalTruncatedHilbert r R f z*star (g z) ∂planeMeasure‖≤
        C*(∫ z, ‖f z‖ ∂planeMeasure)^(1/p)*(∫ z, ‖g z‖ ∂planeMeasure)^(1/q) := by
  obtain ⟨C,hC,hbound⟩ := horizontalHilbert_power_bound hH
  refine ⟨C,hC,?_⟩
  intro p q hp hpq r R hr hrR f g hf hg
  have hp0 := hpq.pos
  have hq0 := hpq.symm.pos
  have hsz := hbound p hp r R hr hrR f
  have hmem : MemLp (horizontalTruncatedHilbert r R f) (ENNReal.ofReal p) planeMeasure := by
    apply (integrable_norm_rpow_iff
      (horizontalTruncatedHilbert_measurable r R f).aestronglyMeasurable
      (by simpa only [ne_eq,ENNReal.ofReal_eq_zero,not_le] using hp0) (by simp)).1
    simpa only [ENNReal.toReal_ofReal hp0.le] using hsz.1
  have hfpower := schwartz_power_le_l1 f hf p hpq.lt.le
  have hgpower := schwartz_power_le_l1 g hg q hpq.symm.lt.le
  have hroot : (∫ z, ‖horizontalTruncatedHilbert r R f z‖^p ∂planeMeasure)^(1/p)≤
      C*(∫ z, ‖f z‖ ∂planeMeasure)^(1/p) := by
    calc
      _ ≤ (C^p*(∫ z, ‖f z‖ ∂planeMeasure))^(1/p) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _)
          (hsz.2.trans (mul_le_mul_of_nonneg_left hfpower (Real.rpow_nonneg hC.le _)))
          (by positivity)
      _ = _ := by
        rw [Real.mul_rpow (Real.rpow_nonneg hC.le _) (integral_nonneg fun _ => norm_nonneg _),
          ←Real.rpow_mul hC.le,mul_one_div_cancel hp0.ne',Real.rpow_one]
  calc
    _ ≤ ∫ z, ‖horizontalTruncatedHilbert r R f z*star (g z)‖ ∂planeMeasure :=
      norm_integral_le_integral_norm _
    _ = ∫ z, ‖horizontalTruncatedHilbert r R f z‖*‖g z‖ ∂planeMeasure := by
      simp only [norm_mul,norm_star]
    _ ≤ (∫ z, ‖horizontalTruncatedHilbert r R f z‖^p ∂planeMeasure)^(1/p)*
        (∫ z, ‖g z‖^q ∂planeMeasure)^(1/q) :=
      integral_mul_norm_le_Lp_mul_Lq hpq hmem (g.memLp _ _)
    _ ≤ _ := mul_le_mul hroot
      (Real.rpow_le_rpow (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _)
        hgpower (by positivity)) (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _)
        (mul_nonneg hC.le (Real.rpow_nonneg (integral_nonneg fun _ => norm_nonneg _) _))

theorem horizontalHilbertProjection_restricted_pairing (hH : HorizontalHilbertInput) :
    ∃ C : ℝ, 0<C ∧ ∀ p q : ℝ, (p=3/2 ∨ p=4) → p.HolderConjugate q →
      ∀ r R : ℝ, 0<r → r≤R → ∀ (cutoff : SchwartzMap ℝ ℂ) (w : ℝ), 0<w →
      ∀ f g : SchwartzMap (ℝ×ℝ) ℂ, (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      ‖∫ z, horizontalTruncatedHilbert r R (schwartzVerticalProjection cutoff w 0 f) z*
        star (g z) ∂planeMeasure‖≤
        (C*verticalProjectionCost cutoff)*(∫ z, ‖f z‖ ∂planeMeasure)^(1/p)*
          (∫ z, ‖g z‖ ∂planeMeasure)^(1/q) := by
  obtain ⟨C,hC,hbound⟩ := horizontalHilbert_restricted_pairing hH
  refine ⟨C,hC,?_⟩
  intro p q hp hpq r R hr hrR cutoff w hw f g hf hg
  have hb := hbound p q hp hpq r R hr hrR (normalizedBandProjection cutoff w f) g
    (normalizedBandProjection_uniform cutoff w hw f hf) hg
  have hs := (normalizedBandProjection_sizes cutoff w hw f).1
  change ‖∫ z, slopeKernelOperator (sharpTimeKernel r R) (fun _ => 0)
    (schwartzVerticalProjection cutoff w 0 f) z*star (g z) ∂planeMeasure‖≤_
  rw [bandProjection_pairing_normalize]
  calc
    _ ≤ verticalProjectionCost cutoff*
        (C*(∫ z, ‖normalizedBandProjection cutoff w f z‖ ∂planeMeasure)^(1/p)*
          (∫ z, ‖g z‖ ∂planeMeasure)^(1/q)) :=
      mul_le_mul_of_nonneg_left hb (verticalProjectionCost_pos _).le
    _ ≤ verticalProjectionCost cutoff*
        (C*(∫ z, ‖f z‖ ∂planeMeasure)^(1/p)*(∫ z, ‖g z‖ ∂planeMeasure)^(1/q)) := by
      apply mul_le_mul_of_nonneg_left _ (verticalProjectionCost_pos _).le
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (integral_nonneg fun _ => norm_nonneg _) _)
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact Real.rpow_le_rpow (integral_nonneg fun _ => norm_nonneg _) hs (one_div_nonneg.mpr hpq.pos.le)
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
