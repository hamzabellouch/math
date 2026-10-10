import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ExteriorDilation

namespace OAI

/-!
# Integrability under dilation of exterior regions

Positive dilation identifies the unit closed exterior with the closed exterior
at the dilation radius. This change of variables transports integrability of
functions on exterior regions to their rescaled compositions.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

theorem preimage_closedExterior_dilation {d : ℕ} (r : ℝ) (hr : 0 < r) :
    (fun x : Ambient d => r • x) ⁻¹' closedExterior 0 r = closedExterior 0 1 := by
  ext x
  simp only [mem_preimage, closedExterior, mem_ofPred_eq, dist_zero_left,
    norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  constructor <;> intro h <;> nlinarith

theorem integrableOn_closedExterior_comp_smul {d : ℕ}
    (f : Ambient d → ℝ) (r : ℝ) (hr : 0 < r)
    (hi : IntegrableOn f (closedExterior 0 r)) :
    IntegrableOn (fun x => f (r • x)) (closedExterior (0 : Ambient d) 1) := by
  have hh := (hi.integrable_indicator (closedExterior_measurable 0 r)).comp_smul hr.ne'
  apply (integrable_indicator_iff (closedExterior_measurable (0 : Ambient d) 1)).mp
  apply hh.congr
  filter_upwards with x
  have hx : r • x ∈ closedExterior 0 r ↔ x ∈ closedExterior 0 1 := by
    change x ∈ (fun x : Ambient d => r • x) ⁻¹' closedExterior 0 r ↔ _
    rw [preimage_closedExterior_dilation r hr]
  by_cases hs : x ∈ closedExterior (0 : Ambient d) 1
  · rw [Set.indicator_of_mem (hx.mpr hs), Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem (fun h => hs (hx.mp h)), Set.indicator_of_notMem hs]

theorem exterior_weighted_normalized_dilation_integrable {d : ℕ} (q k : ℕ)
    (f : Ambient d → ℂ) (r : ℝ) (hr : 0 < r)
    (hi : IntegrableOn (fun x => ‖f x‖ * inverseDistancePow q 0 x) (closedExterior 0 r)) :
    IntegrableOn (fun x => ‖((r : ℂ) ^ k)⁻¹ * f (r • x)‖ * inverseDistancePow q 0 x)
      (closedExterior (0 : Ambient d) 1) := by
  have hh := (integrableOn_closedExterior_comp_smul
    (fun x => ‖f x‖ * inverseDistancePow q 0 x) r hr hi).const_mul (r ^ q * (r ^ k)⁻¹)
  apply hh.congr
  filter_upwards with x
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    inverseDistancePow_origin_smul q r hr]
  have hz : r ^ q ≠ 0 := pow_ne_zero _ hr.ne'
  field_simp

end

end RieszRectifiability

end OAI
