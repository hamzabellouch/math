import OAI.Probability.FreeIsing.Brownian.IntegralHorizon

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*}

theorem uniformGrid_mul_nat_horizon (T : ℝ≥0) {b : ℕ} (hb : 0 < b)
    (n i : ℕ) :
    BrownianGrid.uniformGrid ((b : ℝ≥0) * T) (b * n) i =
      BrownianGrid.uniformGrid T n i := by
  have hb0 : (b : ℝ≥0) ≠ 0 := by exact_mod_cast hb.ne'
  by_cases hn : n = 0
  · simp [hn, BrownianGrid.uniformGrid]
  · have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn
    simp only [BrownianGrid.uniformGrid, Nat.cast_mul]
    field_simp

theorem stoppedUniformSum_mul_nat_horizon (B H : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) {b : ℕ} (hb : 0 < b) (n : ℕ) {t : ℝ≥0} (ht : t ≤ T) :
    stoppedUniformSum B H ((b : ℝ≥0) * T) (b * n) t =
      stoppedUniformSum B H T n t := by
  have hg : BrownianGrid.uniformGrid ((b : ℝ≥0) * T) (b * n) =
      BrownianGrid.uniformGrid T n := by
    funext i
    exact uniformGrid_mul_nat_horizon T hb n i
  by_cases hn : n = 0
  · funext ω
    simp [hn, stoppedUniformSum]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    funext ω
    simp only [stoppedUniformSum, hg]
    symm
    apply Finset.sum_subset (Finset.range_mono (by nlinarith : n ≤ b * n))
    intro i hi hni
    have hindex : n ≤ i := Nat.le_of_not_gt (fun h => hni (Finset.mem_range.mpr h))
    have hta : t ≤ BrownianGrid.uniformGrid T n i :=
      ht.trans ((BrownianGrid.uniformGrid_end T hnpos).symm.le.trans
        (BrownianGrid.uniformGrid_mono T n hindex))
    have htb : t ≤ BrownianGrid.uniformGrid T n (i + 1) :=
      hta.trans (BrownianGrid.uniformGrid_mono T n (Nat.le_succ i))
    simp only [StoppedSimpleIntegral.intervalSum, min_eq_left hta,
      min_eq_left htb, sub_self, mul_zero]

theorem uniformSum_nat_div_eq_stopped (B H : ℝ≥0 → Ω → ℝ)
    (a : ℕ) {b : ℕ} (hb : 0 < b) (n : ℕ) :
    BrownianGrid.uniformSum B H ((a : ℝ≥0) / b) n =
      stoppedUniformSum B H a (b * n) ((a : ℝ≥0) / b) := by
  have hb0 : (b : ℝ≥0) ≠ 0 := by exact_mod_cast hb.ne'
  have he : (b : ℝ≥0) * ((a : ℝ≥0) / b) = a := by field_simp
  rw [← stoppedUniformSum_terminal]
  exact (he ▸ stoppedUniformSum_mul_nat_horizon B H
    ((a : ℝ≥0) / b) hb n le_rfl).symm

theorem tendsto_uniformSum_nat_div_of_integer_limits
    [MeasurableSpace Ω] {P : Measure Ω} {B H I : ℝ≥0 → Ω → ℝ}
    (hlim : ∀ (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (stoppedUniformSum B H N n t ω - I t ω) ^ 2 ∂P) atTop (𝓝 0))
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum B H ((a : ℝ≥0) / b) n ω -
        I ((a : ℝ≥0) / b) ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hbone : (1 : ℝ≥0) ≤ b := by exact_mod_cast hb
  have ht : (a : ℝ≥0) / b ≤ a := div_le_self (by positivity) hbone
  have hcofinal : Tendsto (fun n : ℕ => b * n) atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) tendsto_id
    change n ≤ b * n
    have hbn : 1 ≤ b := hb
    simpa only [one_mul] using Nat.mul_le_mul_right n hbn
  simpa only [uniformSum_nat_div_eq_stopped B H a hb, Function.comp_def] using
    (hlim a ha ((a : ℝ≥0) / b) ht).comp hcofinal

theorem tendsto_uniformSum_pos_rat_of_integer_limits
    [MeasurableSpace Ω] {P : Measure Ω} {B H I : ℝ≥0 → Ω → ℝ}
    (hlim : ∀ (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (stoppedUniformSum B H N n t ω - I t ω) ^ 2 ∂P) atTop (𝓝 0))
    (q : ℚ) (hq : 0 < q) :
    Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum B H (q : ℝ).toNNReal n ω -
        I (q : ℝ).toNNReal ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  have hqR : 0 ≤ (q : ℝ) := by exact_mod_cast hq.le
  have hcast : (q.num.toNat : ℝ) = (q.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  have he : (q : ℝ).toNNReal = (q.num.toNat : ℝ≥0) / q.den := by
    apply NNReal.eq
    simp only [Real.coe_toNNReal _ hqR, NNReal.coe_div, NNReal.coe_natCast]
    rw [Rat.cast_def, hcast]
  rw [he]
  exact tendsto_uniformSum_nat_div_of_integer_limits hlim
    (by omega) q.pos

end Problem367.BrownianIntegralProcess

end

end OAI
