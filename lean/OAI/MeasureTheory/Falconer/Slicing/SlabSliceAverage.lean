import OAI.MeasureTheory.Falconer.Radial.SphereSlab
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

namespace OAI

/-! Averaging thin hyperplane slabs before taking their slice limit. -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

noncomputable def slabSliceAverage {n : ℕ} (r : ℝ) (F : Space (n+1) → ℝ≥0∞)
    (w : Sphere (n+1)) : ℝ≥0∞ :=
  (ENNReal.ofReal (2*r))⁻¹ *
    ∫⁻ x : Space (n+1),
      {x : Space (n+1) | |inner ℝ x (w : Space (n+1))| ≤ r}.indicator F x

theorem slabSliceAverage_measurable {n : ℕ} (r : ℝ) {F : Space (n+1) → ℝ≥0∞}
    (hF : Measurable F) : Measurable (slabSliceAverage r F) := by
  unfold slabSliceAverage
  apply Measurable.const_mul
  apply Measurable.lintegral_prod_right
  change Measurable (fun p : Sphere (n+1) × Space (n+1) =>
    if |inner ℝ p.2 (p.1 : Space (n+1))| ≤ r then F p.2 else 0)
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
    (hF.comp measurable_snd) measurable_const

theorem slabSliceAverage_integral_bound (n : ℕ) {r : ℝ} (hr : 0 < r)
    {F : Space (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ w : Sphere (n+1), slabSliceAverage r F w ∂sphereMeasure (n+1)) ≤
      ENNReal.ofReal ((((n+1 : ℕ) : ℝ)*2^(n+1))/2) *
        ∫⁻ x : Space (n+1), F x * (ENNReal.ofReal ‖x‖)⁻¹ := by
  let K : ℝ := ((n+1 : ℕ) : ℝ)*2^(n+1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hm : Measurable (fun p : Sphere (n+1) × Space (n+1) =>
      {x : Space (n+1) | |inner ℝ x (p.1 : Space (n+1))| ≤ r}.indicator F p.2) :=
    show Measurable (fun p : Sphere (n+1) × Space (n+1) =>
      if |inner ℝ p.2 (p.1 : Space (n+1))| ≤ r then F p.2 else 0) from
      Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
        (hF.comp measurable_snd) measurable_const
  have hne : ∀ᵐ x : Space (n+1) ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  unfold slabSliceAverage
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))),
    lintegral_lintegral_swap hm.aemeasurable,
    ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hne] with x hx
  have hinner : (∫⁻ w : Sphere (n+1),
      {z : Space (n+1) | |inner ℝ z (w : Space (n+1))| ≤ r}.indicator F x
        ∂sphereMeasure (n+1)) = F x *
      sphereMeasure (n+1) {w : Sphere (n+1) | |inner ℝ x (w : Space (n+1))| ≤ r} := by
    change (∫⁻ w : Sphere (n+1),
      {w : Sphere (n+1) | |inner ℝ x (w : Space (n+1))| ≤ r}.indicator (fun _ => F x) w
        ∂sphereMeasure (n+1)) = _
    exact lintegral_indicator_const (measurableSet_le (by fun_prop) measurable_const) _
  rw [hinner]
  have hb : sphereMeasure (n+1) {w : Sphere (n+1) | |inner ℝ x (w : Space (n+1))| ≤ r} ≤
      ENNReal.ofReal (K*r/‖x‖) := by
    simpa only [real_inner_comm] using sphere_slab_bound n hx hr.le
  calc
    _ ≤ (ENNReal.ofReal (2*r))⁻¹ * (F x * ENNReal.ofReal (K*r/‖x‖)) :=
      mul_le_mul_right (mul_le_mul_right hb (F x)) _
    _ = ENNReal.ofReal (K/2) * (F x * (ENNReal.ofReal ‖x‖)⁻¹) := by
      have hscalar : (ENNReal.ofReal (2*r))⁻¹ * ENNReal.ofReal (K*r/‖x‖) =
          ENNReal.ofReal (K/2) * (ENNReal.ofReal ‖x‖)⁻¹ := by
        rw [← ENNReal.ofReal_inv_of_pos (by positivity : 0 < 2*r),
          ← ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr hx),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
      calc
        _ = F x * ((ENNReal.ofReal (2*r))⁻¹ * ENNReal.ofReal (K*r/‖x‖)) := by ac_rfl
        _ = _ := by rw [hscalar]; ac_rfl

noncomputable def slabSliceMajorant {n : ℕ} (F : Space (n+1) → ℝ≥0∞)
    (w : Sphere (n+1)) : ℝ≥0∞ :=
  liminf (fun k : ℕ => slabSliceAverage (1/((k : ℝ)+1)) F w) atTop

theorem slabSliceMajorant_measurable {n : ℕ} {F : Space (n+1) → ℝ≥0∞}
    (hF : Measurable F) : Measurable (slabSliceMajorant F) :=
  Measurable.liminf (fun k => slabSliceAverage_measurable (1/((k : ℝ)+1)) hF)

theorem slabSliceMajorant_integral_bound (n : ℕ) {F : Space (n+1) → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ w : Sphere (n+1), slabSliceMajorant F w ∂sphereMeasure (n+1)) ≤
      ENNReal.ofReal ((((n+1 : ℕ) : ℝ)*2^(n+1))/2) *
        ∫⁻ x : Space (n+1), F x * (ENNReal.ofReal ‖x‖)⁻¹ := by
  apply (lintegral_liminf_le (fun k => slabSliceAverage_measurable _ hF)).trans
  have h := liminf_le_liminf (f := atTop) (Filter.Eventually.of_forall fun k : ℕ =>
    slabSliceAverage_integral_bound n (r := 1/((k : ℝ)+1)) (by positivity) hF)
  simpa only [liminf_const] using h

end Falconer

end OAI
