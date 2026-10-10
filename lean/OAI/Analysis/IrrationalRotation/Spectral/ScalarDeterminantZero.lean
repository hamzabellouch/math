import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

namespace OAI

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Invariant233.ScalarDeterminant

theorem log_sq_add_sq_le {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    Real.log (a ^ 2 + t ^ 2) ≤ Real.log 2 + 2 * Real.log (max a t) := by
  have hm : 0 < max a t := ht.trans_le (le_max_right a t)
  have ha2 := pow_le_pow_left₀ ha (le_max_left a t) 2
  have ht2 := pow_le_pow_left₀ ht.le (le_max_right a t) 2
  have hlog : Real.log (a ^ 2 + t ^ 2) ≤ Real.log (2 * (max a t) ^ 2) :=
    Real.log_le_log (by positivity) (by linarith)
  calc
    _ ≤ Real.log (2 * (max a t) ^ 2) := hlog
    _ = _ := by rw [Real.log_mul (by norm_num) (pow_ne_zero _ hm.ne'), Real.log_pow]; norm_num

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem integrable_regularized_log {f : X → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x => Real.log (f x ^ 2 + ε)) μ := by
  refine (integrable_const (|Real.log ε| + |Real.log (1 + ε)|)).mono'
    ((hf.pow_const 2 |>.add_const ε).log.aestronglyMeasurable) ?_
  filter_upwards [] with x
  have hx := hbound x
  have hlo : Real.log ε ≤ Real.log (f x ^ 2 + ε) :=
    Real.log_le_log hε (le_add_of_nonneg_left (sq_nonneg _))
  have hhi : Real.log (f x ^ 2 + ε) ≤ Real.log (1 + ε) := by
    apply Real.log_le_log (by positivity)
    nlinarith
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := neg_abs_le (Real.log ε)
    have := abs_nonneg (Real.log (1 + ε))
    linarith
  · have := le_abs_self (Real.log (1 + ε))
    have := abs_nonneg (Real.log ε)
    linarith

theorem integrable_truncated_log {f : X → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {M : ℝ} (hM : 0 < M) :
    Integrable (fun x => Real.log (max (f x) (Real.exp (-M)))) μ := by
  refine (integrable_const M).mono'
    ((hf.max measurable_const).log.aestronglyMeasurable) ?_
  filter_upwards [] with x
  have hp : 0 < max (f x) (Real.exp (-M)) :=
    (Real.exp_pos _).trans_le (le_max_right _ _)
  have hlo : -M ≤ Real.log (max (f x) (Real.exp (-M))) := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos (-M)) (le_max_right (f x) (Real.exp (-M)))
  have hhi : Real.log (max (f x) (Real.exp (-M))) ≤ 0 := by
    apply Real.log_nonpos hp.le
    exact max_le (hbound x).2 (Real.exp_le_one_iff.mpr (by linarith))
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨hlo, hhi.trans hM.le⟩

variable [IsProbabilityMeasure μ]

theorem integral_regularized_log_le {f : X → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {M : ℝ} (hM : 0 < M) :
    (∫ x, Real.log (f x ^ 2 + (Real.exp (-M)) ^ 2) ∂μ) ≤
      Real.log 2 + 2 * ∫ x, Real.log (max (f x) (Real.exp (-M))) ∂μ := by
  have hint := integrable_truncated_log (μ := μ) hf hbound hM
  calc
    _ ≤ ∫ x, Real.log 2 + 2 * Real.log (max (f x) (Real.exp (-M))) ∂μ :=
      integral_mono (integrable_regularized_log hf hbound (sq_pos_of_pos (Real.exp_pos _)))
        ((integrable_const _).add (hint.const_mul 2))
        (fun x => log_sq_add_sq_le (hbound x).1 (Real.exp_pos _))
    _ = _ := by
      rw [integral_add (integrable_const _) (hint.const_mul 2), integral_const_mul]
      simp

theorem regularized_determinant_eq_zero {f : X → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (htrunc : ∀ B : ℝ, ∃ M : ℝ, 0 < M ∧
      (∫ x, Real.log (max (f x) (Real.exp (-M))) ∂μ) < B) :
    (⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
      (Real.exp ((∫ x, Real.log (f x ^ 2 + ε.val) ∂μ) / 2))) = 0 := by
  apply le_antisymm _ bot_le
  have hlow (n : ℕ) :
      (⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
        (Real.exp ((∫ x, Real.log (f x ^ 2 + ε.val) ∂μ) / 2))) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
    obtain ⟨M, hM, hsmall⟩ := htrunc (-(n : ℝ) - Real.log 2 / 2)
    have hint := integral_regularized_log_le (μ := μ) hf hbound hM
    calc
      _ ≤ ENNReal.ofReal (Real.exp
          ((∫ x, Real.log (f x ^ 2 + (Real.exp (-M)) ^ 2) ∂μ) / 2)) :=
        iInf_le _ (⟨(Real.exp (-M)) ^ 2, sq_pos_of_pos (Real.exp_pos _)⟩ : {r : ℝ // 0 < r})
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        linarith
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(n : ℝ))))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop)
  exact ge_of_tendsto' hlim hlow


end Invariant233.ScalarDeterminant

end OAI
