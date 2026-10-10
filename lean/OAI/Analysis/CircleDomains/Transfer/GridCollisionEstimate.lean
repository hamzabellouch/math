import OAI.Analysis.CircleDomains.Transfer.GridCollisions
import OAI.Analysis.CircleDomains.Transfer.ReciprocalGridSelection

namespace OAI

/-!
# Vanishing scaled expectation for the actual collision count

The probability estimates are multiplied by the square of the grid spacing.
This turns the normalized band probabilities into the clipped products
`min h a * min h b`, dominated by summable oscillation products.
Thus the actual random count, with its spacing-dependent law, satisfies the
small-expectation premise of the reciprocal-grid selection theorem.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace CircleDomainRigidity.FiniteTransfer

theorem scaled_pair_probability_eq {h a b : ℝ} (hh : 0 < h) :
    h ^ 2 * (min 1 (a / h) * min 1 (b / h)) = min h a * min h b := by
  have ha : min 1 (a / h) = min h a / h := by
    rw [← min_div_div_right hh.le, div_self hh.ne']
  have hb : min 1 (b / h) = min h b / h := by
    rw [← min_div_div_right hh.le, div_self hh.ne']
  rw [ha, hb]
  field_simp

theorem scaled_lintegral_gridCollisionCount_le {n : ℕ} {P S : Type*}
    [Fintype P] [Countable S] {h : ℝ} (hh : 0 < h)
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2)) :
    ENNReal.ofReal (h ^ 2) *
      (∫⁻ θ, gridCollisionCount h pairs a b θ
        ∂Measure.pi (fun _ : Fin n => shiftLaw h)) ≤
      ENNReal.ofReal (∑ p, ∑' s,
        min h (b (pairs p).1 s - a (pairs p).1 s) *
          min h (b (pairs p).2 s - a (pairs p).2 s)) := by
  have hterm (p : P) (s : S) :
      ENNReal.ofReal (h ^ 2) *
        (ENNReal.ofReal (min 1 ((b (pairs p).1 s - a (pairs p).1 s) / h)) *
          ENNReal.ofReal (min 1 ((b (pairs p).2 s - a (pairs p).2 s) / h))) =
      ENNReal.ofReal (min h (b (pairs p).1 s - a (pairs p).1 s) *
        min h (b (pairs p).2 s - a (pairs p).2 s)) := by
    rw [← ENNReal.ofReal_mul (le_min zero_le_one
      (div_nonneg (hwidth (pairs p).1 s) hh.le)),
      ← ENNReal.ofReal_mul (sq_nonneg h), scaled_pair_probability_eq hh]
  calc
    _ ≤ ENNReal.ofReal (h ^ 2) *
        (∑ p, ∑' s, ENNReal.ofReal (min 1 ((b (pairs p).1 s - a (pairs p).1 s) / h)) *
          ENNReal.ofReal (min 1 ((b (pairs p).2 s - a (pairs p).2 s) / h))) :=
      mul_le_mul_right (lintegral_gridCollisionCount_le hh pairs hpairs a b) _
    _ = ∑ p, ∑' s, ENNReal.ofReal
        (min h (b (pairs p).1 s - a (pairs p).1 s) *
          min h (b (pairs p).2 s - a (pairs p).2 s)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr (hterm p)
    _ = _ := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro p _
        exact (ENNReal.ofReal_tsum_of_nonneg
          (fun s => mul_nonneg (le_min hh.le (hwidth (pairs p).1 s))
            (le_min hh.le (hwidth (pairs p).2 s)))
          (summable_min_mul_min (hwidth (pairs p).1) (hwidth (pairs p).2)
            (hwidth2 (pairs p).1) (hwidth2 (pairs p).2) hh.le)).symm
      · intro p _
        exact tsum_nonneg (fun s => mul_nonneg (le_min hh.le (hwidth (pairs p).1 s))
          (le_min hh.le (hwidth (pairs p).2 s)))

/-- The actual count is integrable, and its ordinary expected value
satisfies the paper's scaled clipped-product estimate. -/
theorem scaled_integral_gridCollisionCount_le {n : ℕ} {P S : Type*}
    [Fintype P] [Countable S] {h : ℝ} (hh : 0 < h)
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2)) :
    Integrable (fun θ => (gridCollisionCount h pairs a b θ).toReal)
      (Measure.pi (fun _ : Fin n => shiftLaw h)) ∧
    h ^ 2 * (∫ θ, (gridCollisionCount h pairs a b θ).toReal
      ∂Measure.pi (fun _ : Fin n => shiftLaw h)) ≤
      ∑ p, ∑' s, min h (b (pairs p).1 s - a (pairs p).1 s) *
        min h (b (pairs p).2 s - a (pairs p).2 s) := by
  have hmeas : Measurable (gridCollisionCount h pairs a b) :=
    measurable_weightedBandIncidence _ _ (fun ps =>
      measurableSet_pairedLatticeIncidence hh _ _ _ _ _ _)
  have hfinite := lintegral_gridCollisionCount_lt_top hh pairs hpairs a b hwidth hwidth2
  refine ⟨integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hfinite.ne, ?_⟩
  rw [integral_toReal hmeas.aemeasurable (ae_lt_top hmeas hfinite.ne)]
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (scaled_lintegral_gridCollisionCount_le hh pairs hpairs a b hwidth hwidth2)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg h),
    ENNReal.toReal_ofReal] at hb
  · exact hb
  · exact Finset.sum_nonneg (fun p _ => tsum_nonneg (fun s =>
      mul_nonneg (le_min hh.le (hwidth (pairs p).1 s))
        (le_min hh.le (hwidth (pairs p).2 s))))

/-- The scaled collision expectation tends to zero along the exact
reciprocal-integer grids and their actual independent shift laws. -/
theorem scaled_gridCollisionCount_mean_tendsto_zero {n : ℕ} {P S : Type*}
    [Fintype P] [Countable S]
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2)) :
    Tendsto (fun N => reciprocalGridStep N ^ 2 *
      (∫ θ, (gridCollisionCount (reciprocalGridStep N) pairs a b θ).toReal
        ∂reciprocalGridLaw n N)) atTop (𝓝 0) := by
  have hstep : Tendsto reciprocalGridStep atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨reciprocalGridStep_tendsto_zero,
      Eventually.of_forall reciprocalGridStep_pos⟩
  have hboundlim : Tendsto (fun N => ∑ p, ∑' s,
      min (reciprocalGridStep N) (b (pairs p).1 s - a (pairs p).1 s) *
        min (reciprocalGridStep N) (b (pairs p).2 s - a (pairs p).2 s))
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero, Function.comp_apply] using
      tendsto_finsetSum Finset.univ (fun p _ =>
        (tendsto_tsum_min_mul_min_zero (hwidth (pairs p).1) (hwidth (pairs p).2)
          (hwidth2 (pairs p).1) (hwidth2 (pairs p).2)).comp hstep)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hboundlim
  · intro N
    exact mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => ENNReal.toReal_nonneg))
  · intro N
    exact (scaled_integral_gridCollisionCount_le (reciprocalGridStep_pos N)
      pairs hpairs a b hwidth hwidth2).2

end CircleDomainRigidity.FiniteTransfer

end OAI
