import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.VectorBesselTransfer

namespace OAI

/-!
# Cell means from native vector norm bounds

Cell means respect addition, subtraction, and constants, and inherit almost-everywhere
uniform bounds. For a vector field controlled in `L²` by a scalar input, its components
along vectors of norm at most one have bounded means on sets of finite positive mass.
The estimate combines the squared norm bound with the scalar input's local energy budget.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

theorem cellMean_add (μ : Measure X) (f g : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    cellMean μ (fun x => f x + g x) = cellMean μ f + cellMean μ g := by
  simp only [cellMean, integral_add hf hg, add_div]

theorem cellMean_sub (μ : Measure X) (f g : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    cellMean μ (fun x => f x - g x) = cellMean μ f - cellMean μ g := by
  simp only [cellMean, integral_sub hf hg, sub_div]

theorem cellMean_const (μ : Measure X) (c : ℝ) (hμ : μ.real univ ≠ 0) :
    cellMean μ (fun _ => c) = c := by
  simp only [cellMean, integral_const, smul_eq_mul]
  exact mul_div_cancel_left₀ c hμ

theorem cellMean_abs_le_ae_bound (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hμ : 0 < μ.real univ) (B : ℝ)
    (hb : ∀ᵐ x ∂μ, |f x| ≤ B) : |cellMean μ f| ≤ B := by
  have hn : ‖∫ x, f x ∂μ‖ ≤ B * μ.real univ :=
    norm_integral_le_of_norm_le_const (by simpa only [Real.norm_eq_abs] using! hb)
  rw [cellMean, abs_div, abs_of_pos hμ]
  exact (div_le_iff₀ hμ).mpr (by simpa only [Real.norm_eq_abs] using! hn)

theorem cellMean_near_constant (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Integrable f μ) (hμ : 0 < μ.real univ) (c B : ℝ)
    (hb : ∀ᵐ x ∂μ, |f x - c| ≤ B) : |cellMean μ f - c| ≤ B := by
  have h := cellMean_abs_le_ae_bound μ (fun x => f x - c) hμ B hb
  rwa [cellMean_sub μ f (fun _ => c) hf (integrable_const c), cellMean_const μ c hμ.ne'] at h

theorem native_vector_cellMean_bound {d : ℕ}
    (μ : Measure X) (A : Set X) (hfin : μ A < ∞) (hpos : 0 < μ.real A)
    (f : X → ℝ) (u : X → Ambient d) (hf : MemLp f 2 μ) (hu : MemLp u 2 μ)
    (D : ℝ≥0) (hN : eLpNorm u 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (e : Ambient d) (he : ‖e‖ ≤ 1) (B : ℝ)
    (henergy : (∫ x, f x ^ 2 ∂μ) ≤ B * μ.real A) :
    |cellMean (μ.restrict A) (fun x => inner ℝ e (u x))| ≤ (D : ℝ) ^ 2 * B + 1 := by
  let : IsFiniteMeasure (μ.restrict A) := ⟨by simpa only [Measure.restrict_apply_univ] using! hfin⟩
  let v := fun x => inner ℝ e (u x)
  have hv := memLp_inner_const_of_vector μ u hu e
  have hpoint (x : X) : (v x) ^ 2 ≤ ‖u x‖ ^ 2 := by
    have hb : |v x| ≤ ‖u x‖ := by
      calc
        _ ≤ ‖e‖ * ‖u x‖ := by
          simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) e (u x)
        _ ≤ 1 * ‖u x‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
        _ = _ := one_mul _
    have hs := mul_self_le_mul_self (abs_nonneg (v x)) hb
    simpa only [← pow_two, sq_abs] using! hs
  have hbound : (∫ x, v x ^ 2 ∂μ.restrict A) ≤
      ((D : ℝ) ^ 2 * B) * μ.real A := by
    calc
      _ ≤ ∫ x, v x ^ 2 ∂μ :=
        integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall fun x => sq_nonneg _) hv.integrable_sq
      _ ≤ ∫ x, ‖u x‖ ^ 2 ∂μ :=
        integral_mono hv.integrable_sq hu.norm.integrable_sq hpoint
      _ ≤ (D : ℝ) ^ 2 * ∫ x, f x ^ 2 ∂μ :=
        vector_sq_integral_of_native_norm_bound μ f u hf hu D hN
      _ ≤ (D : ℝ) ^ 2 * (B * μ.real A) :=
        mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
      _ = _ := by ring
  have h := cellMean_abs_bound (μ.restrict A) v (hv.restrict A) (μ.real A)
    (((D : ℝ) ^ 2 * B) * μ.real A) hpos (by simp [Measure.real]) hbound
  simpa only [mul_div_cancel_right₀ _ hpos.ne'] using! h

end

end RieszRectifiability

end OAI
