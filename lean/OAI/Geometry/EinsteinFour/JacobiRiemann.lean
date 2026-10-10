import OAI.Geometry.EinsteinFour.JacobiApproximation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! Quantitative Riemann sums for the smooth matrix curves in the radial comparison. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem uniform_mesh_remainder {F f : ℝ → E} {h L : ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hF : ∀ s, HasDerivAt F (f s) s)
    (hf : ∀ s t, ‖f s - f t‖ ≤ L * |s - t|) (N : ℕ) :
    ‖F (N * h) - F 0 - h • (∑ i ∈ Finset.range N, f (i * h))‖ ≤ N * L * h ^ 2 := by
  have htel : ∑ i ∈ Finset.range N, (F ((i + 1) * h) - F (i * h)) = F (N * h) - F 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        abel
  have hid : F (N * h) - F 0 - h • (∑ i ∈ Finset.range N, f (i * h)) =
      ∑ i ∈ Finset.range N, (F ((i + 1) * h) - F (i * h) - h • f (i * h)) := by
    rw [Finset.sum_sub_distrib, htel, Finset.smul_sum]
  rw [hid]
  calc
    _ ≤ ∑ i ∈ Finset.range N, ‖F ((i + 1) * h) - F (i * h) - h • f (i * h)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range N, L * h ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hb := first_order_remainder hh hL (a := i * h) (f := F) (d := f)
        (fun s _ => hF s) (fun s hs => by
          simpa only [abs_of_nonneg (sub_nonneg.mpr hs.1)] using hf s (i * h))
      simpa only [add_mul, one_mul] using hb
    _ = _ := by simp [mul_assoc]

theorem uniform_mesh_tendsto_antiderivative {F f : ℝ → E} {t L : ℝ}
    (ht : 0 ≤ t) (hL : 0 ≤ L)
    (hF : ∀ s, HasDerivAt F (f s) s)
    (hf : ∀ s r, ‖f s - f r‖ ≤ L * |s - r|) :
    Tendsto (fun N : ℕ => (t / N) • (∑ i ∈ Finset.range N, f (i * (t / N)) ))
      atTop (nhds (F t - F 0)) := by
  apply (converges_of_inverse_mesh_error (v := fun _ => (0 : E)) (V := 0)
    (C := L * t ^ 2) ?_).1
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hb := uniform_mesh_remainder (div_nonneg ht (Nat.cast_nonneg N)) hL hF hf N
  have hid : (N : ℝ) * (t / N) = t := by field_simp
  rw [hid, norm_sub_rev] at hb
  simpa only [sub_zero, norm_zero, add_zero, show (N : ℝ) * L * (t / N) ^ 2 =
    L * t ^ 2 / N by field_simp] using hb

variable [CompleteSpace E]

/-- The left mesh sums converge to the actual interval integral. -/
theorem uniform_mesh_tendsto_integral {f : ℝ → E} {t L : ℝ}
    (ht : 0 ≤ t) (hL : 0 ≤ L) (hc : Continuous f)
    (hf : ∀ s r, ‖f s - f r‖ ≤ L * |s - r|) :
    Tendsto (fun N : ℕ => (t / N) • (∑ i ∈ Finset.range N, f (i * (t / N))))
      atTop (nhds (∫ s in (0 : ℝ)..t, f s)) := by
  have hF : ∀ s, HasDerivAt (fun r => ∫ u in (0 : ℝ)..r, f u) (f s) s := by
    intro s
    exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa only [intervalIntegral.integral_same, sub_zero] using
    uniform_mesh_tendsto_antiderivative ht hL hF hf

end

end PositiveEinsteinFour.Jacobi

end OAI
