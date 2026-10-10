import OAI.NumberTheory.JointDickman.Arithmetic.PrimeTupleIntegral
import OAI.NumberTheory.JointDickman.Amplification.SublevelContinuity
import OAI.NumberTheory.JointDickman.Amplification.MovingMonotoneLimit

namespace OAI

/-! # The actual counting scale in the reciprocal prime-tuple limit -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem primeLogProduct_moving_box_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (n : ℕ) (a b : Fin (n+1) → ℝ) {v : ℝ → ℝ} {u : ℝ}
    (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun x => ((FiniteMeasure.pi (fun _ : Fin (n+1) => primeLogMeasure c x))
      (primeBoxCutoff (n+1) a b (v x)) : ℝ)) atTop
      (𝓝 ((FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
        (primeBoxCutoff (n+1) a b u) : ℝ)) := by
  apply moving_monotone_tendsto _ (primeLogProduct_box_tendsto hc hc1 n a b)
    (primeBoxCutoff_measure_continuous n a b).continuousAt hv
  intro x s t hst
  apply NNReal.coe_le_coe.mpr
  apply FiniteMeasure.apply_mono
  rintro y ⟨hy,hys⟩
  exact ⟨hy,hys.trans hst⟩

theorem log_scaled_ratio_tendsto {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ => Real.log (A*x)/Real.log x) atTop (𝓝 1) := by
  have ht := (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop :
    Tendsto (fun x : ℝ => Real.log A/Real.log x) atTop (𝓝 0)).const_add 1
  apply (show Tendsto (fun x : ℝ => 1+Real.log A/Real.log x) atTop (𝓝 1) by simpa using ht).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [Real.log_mul hA.ne' (zero_lt_one.trans hx).ne']
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp
  ring

theorem rpow_log_ratio {x y : ℝ} (hx : 1 < x) (hy : 0 < y) :
    x^(Real.log y/Real.log x) = y := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx)]
  have he : Real.log x*(Real.log y/Real.log x) = Real.log y := by
    field_simp [(Real.log_pos hx).ne']
  rw [he, Real.exp_log hy]

open Classical in
theorem reciprocalPrimeTuple_scaled_box_tendsto {c A : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hA : 0 < A) (n : ℕ) (a b : Fin (n+1) → ℝ) :
    Tendsto (fun x : ℝ =>
      ∑ v ∈ Fintype.piFinset (fun _ : Fin (n+1) => largePrimeSet x (x^c)),
        if (∀ i, x^(a i) < v i ∧ (v i : ℝ) ≤ x^(b i)) ∧
            (∏ i, (v i : ℝ)) ≤ A*x then ∏ i, 1/(v i : ℝ) else 0) atTop
      (𝓝 ((FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
        (primeBoxCutoff (n+1) a b 1) : ℝ)) := by
  apply (primeLogProduct_moving_box_tendsto hc hc1 n a b (log_scaled_ratio_tendsto hA)).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [primeLogProduct_box_apply hx, rpow_log_ratio hx (mul_pos hA (zero_lt_one.trans hx))]

end JointDickman

end OAI
