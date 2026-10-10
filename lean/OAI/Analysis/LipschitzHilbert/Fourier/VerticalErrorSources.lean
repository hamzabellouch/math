import OAI.Analysis.LipschitzHilbert.Estimates.PositiveErrorMajorant

namespace OAI

/-! Averaging the error sources with the common vertical kernel preserves
the pointwise and summed bounds used on every reference line. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem positiveConvolution_finset_sum {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (hf : ∀ j, Measurable (f j)) {C l : ℝ}
    (hl : 0 < l) (hbound : ∀ j s, ‖f j s‖ ≤ C) (x : ℝ) :
    positiveConvolution l (fun s => ∑ j, f j s) x = ∑ j, positiveConvolution l (f j) x := by
  unfold positiveConvolution
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun j _ => positiveConvolution_integrable_at (hf j) hl (hbound j) x)

theorem verticalConvolution_measurable {f : ℝ × ℝ → ℝ} (hf : Measurable f) (W y : ℝ) :
    Measurable (fun x => positiveConvolution W (fun z => f (x,z)) y) := by
  have hm : Measurable (fun p : ℝ × ℝ => lineKernel W (y-p.2) * f p) :=
    ((lineKernel_continuous W).measurable.comp (measurable_const.sub measurable_snd)).mul hf
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

def verticalErrorSources {N : ℕ} (f : Fin N → ℝ × ℝ → ℝ)
    (hf : ∀ j, Measurable (f j)) (L W y C M : ℝ)
    (hL : 0 < L) (hW : 0 < W) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hf0 : ∀ j p, 0 ≤ f j p) (hfC : ∀ j p, f j p ≤ C)
    (hfM : ∀ p, ∑ j, f j p ≤ M) : LineErrorSources N where
  topLength := L
  topLength_pos := hL
  sourceBound := C * Real.pi
  sourceBound_nonneg := mul_nonneg hC Real.pi_pos.le
  sumBound := M * Real.pi
  sumBound_nonneg := mul_nonneg hM Real.pi_pos.le
  source := fun j x => positiveConvolution W (fun z => f j (x,z)) y
  measurable_source := fun j => verticalConvolution_measurable (hf j) W y
  source_nonneg := fun j x => positiveConvolution_nonneg hW (fun z => hf0 j (x,z)) y
  source_bound := by
    intro j x
    have hf' : Measurable (fun z => f j (x,z)) := (hf j).comp (measurable_const.prodMk measurable_id)
    have hb (z : ℝ) : ‖f j (x,z)‖ ≤ C := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 j (x,z))]
      exact hfC j (x,z)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using positiveConvolution_le hf' hW hC hb y)
  source_sum := by
    intro x
    have hf' (j : Fin N) : Measurable (fun z => f j (x,z)) :=
      (hf j).comp (measurable_const.prodMk measurable_id)
    have hb (j : Fin N) (z : ℝ) : ‖f j (x,z)‖ ≤ C := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 j (x,z))]
      exact hfC j (x,z)
    rw [← positiveConvolution_finset_sum (fun j z => f j (x,z)) hf' hW hb y]
    have hs : Measurable (fun z => ∑ j, f j (x,z)) :=
      Finset.measurable_sum _ (fun j _ => hf' j)
    have hbs (z : ℝ) : ‖∑ j, f j (x,z)‖ ≤ M := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun j _ => hf0 j (x,z)))]
      exact hfM (x,z)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using positiveConvolution_le hs hW hM hbs y)

end LipschitzHilbert

end

end OAI
