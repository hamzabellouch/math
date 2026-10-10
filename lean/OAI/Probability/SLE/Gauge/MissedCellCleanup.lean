import OAI.Probability.SLE.Gauge.CoverNumerics

namespace OAI

/-! The planar grid count cancels the gauge and hitting exponents in the
missed-cell contribution to the dense cover. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

theorem missed_cell_sum_bound {ι : Type*} (I : Finset ι)
    (cost prob : ι → ℝ≥0∞) (κ r n c A B D : ℝ)
    (hr : 0 < r) (hn : 0 ≤ Real.log n) (_hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hcard : (I.card : ℝ) ≤ A * r ^ (-2 : ℝ))
    (hcost : ∀ i ∈ I, cost i ≤ ENNReal.ofReal
      (B * r ^ dimension κ * (Real.log n) ^ (codimension κ / 2)))
    (hprob : ∀ i ∈ I, prob i ≤ ENNReal.ofReal
      (D * r ^ codimension κ * Real.exp (-c * Real.sqrt n))) :
    ∑ i ∈ I, cost i * prob i ≤ ENNReal.ofReal
      (A * B * D * (Real.log n) ^ (codimension κ / 2) *
        Real.exp (-c * Real.sqrt n)) := by
  have hb0 : 0 ≤ B * r ^ dimension κ * (Real.log n) ^ (codimension κ / 2) :=
    mul_nonneg (mul_nonneg hB (Real.rpow_nonneg hr.le _)) (Real.rpow_nonneg hn _)
  have hd0 : 0 ≤ D * r ^ codimension κ * Real.exp (-c * Real.sqrt n) :=
    mul_nonneg (mul_nonneg hD (Real.rpow_nonneg hr.le _)) (Real.exp_pos _).le
  calc
    _ ≤ ∑ _i ∈ I, ENNReal.ofReal
        (B * r ^ dimension κ * (Real.log n) ^ (codimension κ / 2)) *
        ENNReal.ofReal (D * r ^ codimension κ * Real.exp (-c * Real.sqrt n)) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul' (hcost i hi) (hprob i hi))
    _ = ENNReal.ofReal ((I.card : ℝ) *
        ((B * r ^ dimension κ * (Real.log n) ^ (codimension κ / 2)) *
          (D * r ^ codimension κ * Real.exp (-c * Real.sqrt n)))) := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_mul hb0,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal ((A * r ^ (-2 : ℝ)) *
        ((B * r ^ dimension κ * (Real.log n) ^ (codimension κ / 2)) *
          (D * r ^ codimension κ * Real.exp (-c * Real.sqrt n)))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (mul_nonneg hb0 hd0))
    _ = _ := by
      congr 1
      calc
        _ = (r ^ (-2 : ℝ) * r ^ dimension κ * r ^ codimension κ) *
            (A * B * D * (Real.log n) ^ (codimension κ / 2) *
              Real.exp (-c * Real.sqrt n)) := by ring
        _ = _ := by rw [dense_cover_power_cancellation κ hr, one_mul]

/-- The missed-cell cost vanishes even when its finite prefactor depends on
the compact interior cutoff. The leading sausage charge does not depend on it. -/
theorem missed_cell_sum_tendsto_zero {ι : Type*}
    (I : ℕ → Finset ι) (cost prob : ℕ → ι → ℝ≥0∞)
    (κ : ℝ) (hκ : 0 < κ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (c : ℝ) (hc : 0 < c) (A B D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hcard : ∀ n, ((I n).card : ℝ) ≤ A * r n ^ (-2 : ℝ))
    (hcost : ∀ n i, i ∈ I n → cost n i ≤ ENNReal.ofReal
      (B * r n ^ dimension κ * (Real.log (n : ℝ)) ^ (codimension κ / 2)))
    (hprob : ∀ n i, i ∈ I n → prob n i ≤ ENNReal.ofReal
      (D * r n ^ codimension κ * Real.exp (-c * Real.sqrt (n : ℝ)))) :
    Tendsto (fun n => ∑ i ∈ I n, cost n i * prob n i) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal
      (A * B * D * (Real.log (n : ℝ)) ^ (codimension κ / 2) *
        Real.exp (-c * Real.sqrt (n : ℝ)))) atTop (𝓝 0) := by
    have ht := (explicit_cleanup_tendsto_zero hκ hc).const_mul (A * B * D)
    simpa only [Function.comp_def, mul_assoc, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le)
    (fun n => missed_cell_sum_bound (I n) (cost n) (prob n) κ (r n) n c A B D
      (hr n) (Real.log_natCast_nonneg n) hA hB hD (hcard n) (hcost n) (hprob n))

end SLEExactGauge

end

end OAI
