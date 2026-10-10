import OAI.Analysis.LipschitzHilbert.Estimates.VariationDifference
import OAI.Analysis.LipschitzHilbert.Estimates.MeanOscillation

namespace OAI

/-! The local BMO step for variation: short-scale L1 control and
long-scale oscillation control imply mean oscillation of the full variation. -/

noncomputable section
open MeasureTheory Set

namespace LipschitzHilbert

theorem variation_short_long_mean_oscillation {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasure μ] (S L : ℕ → X → E) (N : ℕ)
    (hs : Integrable (fun x => cubicVariation (fun n => S n x) N) μ)
    (hl : Integrable (fun x => cubicVariation (fun n => L n x) N) μ)
    (hf : Integrable (fun x => cubicVariation (fun n => S n x + L n x) N) μ)
    (hm : 0 < μ.real univ) {K C : ℝ}
    (hshort : (∫ x, cubicVariation (fun n => S n x) N ∂μ) ≤ K * μ.real univ)
    (hlong : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
      cubicVariation (fun n => L n x - L n y) N ≤ C) :
    (∫ x, |cubicVariation (fun n => S n x + L n x) N -
      integralAverage μ (fun y => cubicVariation (fun n => S n y + L n y) N)| ∂μ) ≤
        (2 * K + C) * μ.real univ := by
  let f := fun x => cubicVariation (fun n => S n x + L n x) N
  let g := fun x => cubicVariation (fun n => L n x) N
  have hfg : Integrable (fun x => f x - g x) μ := hf.sub hl
  have hshort' : (∫ x, ‖f x - g x‖ ∂μ) ≤ K * μ.real univ := by
    apply le_trans (integral_mono hfg.norm hs _) hshort
    intro x
    simpa only [Real.norm_eq_abs] using
      abs_cubicVariation_add_sub_le (fun n => S n x) (fun n => L n x) N
  have hlong' : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ‖g x - g y‖ ≤ C := by
    filter_upwards [hlong] with x hx
    filter_upwards [hx] with y hy
    simpa only [Real.norm_eq_abs] using
      (abs_cubicVariation_sub_le (fun n => L n x) (fun n => L n y) N).trans hy
  have h := short_long_mean_oscillation μ (fun x => f x - g x) g hfg hl hm hshort' hlong'
  have heq : (fun x => (f x - g x) + g x) = f := by funext x; ring
  rw [heq] at h
  simpa only [sub_add_cancel, Real.norm_eq_abs] using h

end LipschitzHilbert

end

end OAI
