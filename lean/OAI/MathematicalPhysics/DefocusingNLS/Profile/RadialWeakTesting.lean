import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! Bounded radial potentials: smooth testing determines every L1 pairing. -/

open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_bounded_testing_L1 (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (q : ℕ → ℝ → ℝ) (q₀ : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hq : ∀ n, AEStronglyMeasurable (q n) μ) (hq₀ : AEStronglyMeasurable q₀ μ)
    (hqb : ∀ n, ∀ᵐ r ∂μ, ‖q n r‖ ≤ M) (hq₀b : ∀ᵐ r ∂μ, ‖q₀ r‖ ≤ M)
    (hTest : ∀ g : ℝ → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
      Tendsto (fun n => ∫ r, q n r*g r ∂μ) atTop (𝓝 (∫ r, q₀ r*g r ∂μ)))
    (φ : ℝ → ℝ) (hφ : Integrable φ μ) :
    Tendsto (fun n => ∫ r, q n r*φ r ∂μ) atTop (𝓝 (∫ r, q₀ r*φ r ∂μ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε/(4*(M+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ*(4*(M+1))=ε := div_mul_cancel₀ _ (by positivity)
  obtain ⟨g,hgc,hgs,hgerr⟩ := (memLp_one_iff_integrable.mpr hφ).exist_eLpNorm_sub_le
    (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) le_rfl hδ
  have hg : Integrable g μ := hgs.continuous.integrable_of_hasCompactSupport hgc
  have herr : (∫ r, ‖φ r-g r‖ ∂μ) ≤ δ := by
    calc
      _ = (eLpNorm (φ-g) 1 μ).toReal := by
        change (∫ r, ‖(φ-g) r‖ ∂μ)=(eLpNorm (φ-g) 1 μ).toReal
        rw [eLpNorm_one_eq_lintegral_enorm (hφ.aestronglyMeasurable.sub hg.aestronglyMeasurable),
          integral_norm_eq_lintegral_enorm (hφ.aestronglyMeasurable.sub hg.aestronglyMeasurable)]
      _ ≤ (ENNReal.ofReal δ).toReal := ENNReal.toReal_mono (by simp) hgerr
      _ = δ := ENNReal.toReal_ofReal hδ.le
  have hbound (f : ℝ → ℝ) (hf : AEStronglyMeasurable f μ) (hfb : ∀ᵐ r ∂μ, ‖f r‖ ≤ M) :
      ‖(∫ r, f r*φ r ∂μ)-(∫ r, f r*g r ∂μ)‖ ≤ M*δ := by
    have hiφ := hφ.bdd_mul hf hfb
    have hig := hg.bdd_mul hf hfb
    have hie := (hφ.sub hg).bdd_mul hf hfb
    have he : (∫ r, f r*φ r ∂μ)-(∫ r, f r*g r ∂μ)=∫ r, f r*(φ r-g r) ∂μ := by
      rw [← integral_sub hiφ hig]
      congr 1
      funext r
      ring
    rw [he]
    calc
      _ ≤ ∫ r, ‖f r*(φ r-g r)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ r, M*‖φ r-g r‖ ∂μ := integral_mono_ae hie.norm ((hφ.sub hg).norm.const_mul M)
        (hfb.mono (fun r hr => by
          change ‖f r*(φ r-g r)‖ ≤ M*‖φ r-g r‖
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right hr (norm_nonneg _)))
      _ = M*∫ r, ‖φ r-g r‖ ∂μ := integral_const_mul M _
      _ ≤ M*δ := mul_le_mul_of_nonneg_left herr hM
  have ht := (Metric.tendsto_nhds.mp (hTest g hgc hgs)) (ε/2) (by positivity)
  filter_upwards [ht] with n hn
  rw [dist_eq_norm] at hn ⊢
  have htri := @norm_add₃_le ℝ _
    ((∫ r, q n r*φ r ∂μ)-(∫ r, q n r*g r ∂μ))
    ((∫ r, q n r*g r ∂μ)-(∫ r, q₀ r*g r ∂μ))
    ((∫ r, q₀ r*g r ∂μ)-(∫ r, q₀ r*φ r ∂μ))
  have he : ((∫ r, q n r*φ r ∂μ)-(∫ r, q n r*g r ∂μ))+
      ((∫ r, q n r*g r ∂μ)-(∫ r, q₀ r*g r ∂μ))+
      ((∫ r, q₀ r*g r ∂μ)-(∫ r, q₀ r*φ r ∂μ))=
      (∫ r, q n r*φ r ∂μ)-(∫ r, q₀ r*φ r ∂μ) := by ring
  rw [he,norm_sub_rev (∫ r, q₀ r*g r ∂μ)] at htri
  have hbn := hbound (q n) (hq n) (hqb n)
  have hb₀ := hbound q₀ hq₀ hq₀b
  nlinarith

end DefocusingNLS

end OAI
