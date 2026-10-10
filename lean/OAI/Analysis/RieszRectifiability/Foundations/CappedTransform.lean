import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CappedRieszKernel
import OAI.Analysis.RieszRectifiability.Kernel.HardBilinearPairing

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter
open scoped BoundedContinuousFunction

def scalarCappedTransform {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (e : Ambient d) (ε : ℝ) (f : Ambient d → ℝ) (x : Ambient d) : ℝ :=
  ∫ y, f y * scalarCappedRieszKernel m e ε (x, y) ∂μ

theorem scalarCappedTransform_integrable_and_bound {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f : Ambient d → ℝ) (hfm : Measurable f) (hf : Integrable f μ) (x : Ambient d) :
    Integrable (fun y => f y * scalarCappedRieszKernel m e ε (x, y)) μ ∧
      |scalarCappedTransform m μ e ε f x| ≤ (∫ y, |f y| ∂μ) * (‖e‖ * (ε ^ m)⁻¹) := by
  have hm : Measurable (fun y => f y * scalarCappedRieszKernel m e ε (x, y)) :=
    hfm.mul ((scalarCappedRieszKernel_continuous m e ε hε).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hb (y : Ambient d) : |f y * scalarCappedRieszKernel m e ε (x, y)| ≤
      |f y| * (‖e‖ * (ε ^ m)⁻¹) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (scalarCappedRieszKernel_bound m e ε hε (x, y)) (abs_nonneg _)
  have hI : Integrable (fun y => f y * scalarCappedRieszKernel m e ε (x, y)) μ := by
    apply (hf.abs.mul_const (‖e‖ * (ε ^ m)⁻¹)).mono' hm.aestronglyMeasurable
    exact Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using! hb y
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ y, |f y * scalarCappedRieszKernel m e ε (x, y)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ y, |f y| * (‖e‖ * (ε ^ m)⁻¹) ∂μ :=
      integral_mono hI.abs (hf.abs.mul_const (‖e‖ * (ε ^ m)⁻¹)) hb
    _ = _ := integral_mul_const _ _

theorem scalarCappedTransform_continuous {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f : Ambient d → ℝ) (hfm : Measurable f) (hf : Integrable f μ) :
    Continuous (scalarCappedTransform m μ e ε f) := by
  apply continuous_of_dominated (bound := fun y => |f y| * (‖e‖ * (ε ^ m)⁻¹))
  · intro x
    exact (scalarCappedTransform_integrable_and_bound m μ e ε hε f hfm hf x).1.aestronglyMeasurable
  · intro x
    apply Eventually.of_forall
    intro y
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (scalarCappedRieszKernel_bound m e ε hε (x, y)) (abs_nonneg _)
  · exact hf.abs.mul_const _
  · exact Eventually.of_forall fun y => continuous_const.mul
      ((scalarCappedRieszKernel_continuous m e ε hε).comp (continuous_id.prodMk continuous_const))

theorem exists_boundedContinuous_scalarCappedTransform {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f : Ambient d → ℝ) (hfm : Measurable f) (hf : Integrable f μ) :
    ∃ T : Ambient d →ᵇ ℝ, ∀ x, T x = scalarCappedTransform m μ e ε f x := by
  let B := (∫ y, |f y| ∂μ) * (‖e‖ * (ε ^ m)⁻¹)
  let T : Ambient d →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨scalarCappedTransform m μ e ε f, scalarCappedTransform_continuous m μ e ε hε f hfm hf⟩
    (2 * B) (by
      intro x y
      change dist (scalarCappedTransform m μ e ε f x) (scalarCappedTransform m μ e ε f y) ≤ 2 * B
      rw [Real.dist_eq]
      have hx := (scalarCappedTransform_integrable_and_bound m μ e ε hε f hfm hf x).2
      have hy := (scalarCappedTransform_integrable_and_bound m μ e ε hε f hfm hf y).2
      have ht := abs_sub_le (scalarCappedTransform m μ e ε f x) 0 (scalarCappedTransform m μ e ε f y)
      simp only [sub_zero, zero_sub, abs_neg] at ht
      dsimp only [B]
      linarith)
  exact ⟨T, fun _ => rfl⟩

theorem capped_bilinear_eq_scalarCappedTransform {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarCappedRieszKernel m e ε q ∂μ.prod μ) =
      ∫ x, g x * scalarCappedTransform m μ e ε f x ∂μ := by
  have hI := bounded_kernel_bilinear_integrable μ (scalarCappedRieszKernel m e ε)
    (scalarCappedRieszKernel_continuous m e ε hε).measurable (‖e‖ * (ε ^ m)⁻¹)
    (scalarCappedRieszKernel_bound m e ε hε) g f hgm hfm hg hf
  rw [integral_prod _ hI]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  simp only [mul_assoc, integral_const_mul]
  rfl

end

end RieszRectifiability

end OAI
