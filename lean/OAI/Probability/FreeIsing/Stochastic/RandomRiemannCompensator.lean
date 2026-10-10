import OAI.Probability.FreeIsing.Energy.EnergyRiemannApproximation

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace Problem367.RandomRiemann

def partitionSum (f : ℝ → ℝ) (τ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (τ (i + 1) - τ i) * f (τ i)

theorem abs_partitionSum_le {f : ℝ → ℝ} {τ : ℕ → ℝ} (hτ : Monotone τ)
    (n : ℕ) {C : ℝ} (hb : ∀ i < n, |f (τ i)| ≤ C) :
    |partitionSum f τ n| ≤ C * (τ n - τ 0) := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, |(τ (i + 1) - τ i) * f (τ i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, C * (τ (i + 1) - τ i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hτ (Nat.le_succ i)))]
      nlinarith [mul_le_mul_of_nonneg_left (hb i (Finset.mem_range.mp hi))
        (sub_nonneg.mpr (hτ (Nat.le_succ i)))]
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub]

theorem partition_error_le {f : ℝ → ℝ} (hf : Continuous f)
    {τ : ℕ → ℝ} (hτ : Monotone τ) (n : ℕ) {ε : ℝ}
    (hmod : ∀ i < n, ∀ x ∈ Icc (τ i) (τ (i + 1)), |f (τ i) - f x| ≤ ε) :
    |partitionSum f τ n - ∫ x in τ 0..τ n, f x| ≤ ε * (τ n - τ 0) := by
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := τ) (n := n) (fun i _ => hf.intervalIntegrable _ _)
  have heq : partitionSum f τ n - (∫ x in τ 0..τ n, f x) =
      ∑ i ∈ Finset.range n, ∫ x in τ i..τ (i + 1), f (τ i) - f x := by
    rw [partitionSum, ← hsplit, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ Finset.range n, |∫ x in τ i..τ (i + 1), f (τ i) - f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, ε * (τ (i + 1) - τ i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hle := hτ (Nat.le_succ i)
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := τ i) (b := τ (i + 1)) (C := ε)
        (f := fun x => f (τ i) - f x) (fun x hx => ?_)
      · simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)] using h
      · rw [uIoc_of_le hle] at hx
        exact hmod i (Finset.mem_range.mp hi) x ⟨hx.1.le, hx.2⟩
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub]

def stoppedPoint (T t : ℝ) (n i : ℕ) : ℝ := min t (EnergyRiemann.point T n i)

def stoppedSum (f : ℝ → ℝ) (T t : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    (stoppedPoint T t n (i + 1) - stoppedPoint T t n i) * f (EnergyRiemann.point T n i)

theorem stoppedPoint_mono {T : ℝ} (hT : 0 ≤ T) (t : ℝ) (n : ℕ) :
    Monotone (stoppedPoint T t n) := fun _ _ hij =>
  min_le_min_left t (EnergyRiemann.point_mono hT n hij)

theorem stoppedPoint_zero (T : ℝ) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    stoppedPoint T t n 0 = 0 := by simp [stoppedPoint, ht]

theorem stoppedPoint_end (T t : ℝ) {n : ℕ} (hn : 0 < n) :
    stoppedPoint T t n n = min t T := by rw [stoppedPoint, EnergyRiemann.point_end T hn]

theorem stoppedPoint_step_le {T : ℝ} (hT : 0 ≤ T) (t : ℝ) (n i : ℕ) :
    stoppedPoint T t n (i + 1) - stoppedPoint T t n i ≤ T / n := by
  have hle := EnergyRiemann.point_mono hT n (Nat.le_succ i)
  have hstep := EnergyRiemann.point_step T n i
  unfold stoppedPoint
  by_cases hi : EnergyRiemann.point T n i ≤ t
  · rw [min_eq_right hi]
    exact (sub_le_sub_right (min_le_right t _) _).trans_eq hstep
  · have ht : t ≤ EnergyRiemann.point T n i := le_of_not_ge hi
    rw [min_eq_left ht, min_eq_left (ht.trans hle), sub_self]
    positivity

theorem stoppedSum_eq_partitionSum {T : ℝ} (hT : 0 ≤ T)
    (f : ℝ → ℝ) (t : ℝ) (n : ℕ) :
    stoppedSum f T t n = partitionSum f (stoppedPoint T t n) n := by
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hit : EnergyRiemann.point T n i ≤ t
  · simp only [stoppedPoint, min_eq_right hit]
  · have ht : t ≤ EnergyRiemann.point T n i := le_of_not_ge hit
    have ht' := ht.trans (EnergyRiemann.point_mono hT n (Nat.le_succ i))
    simp only [stoppedPoint, min_eq_left ht, min_eq_left ht', sub_self, zero_mul]

theorem abs_stoppedSum_le {T t C : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t)
    {f : ℝ → ℝ} (hb : ∀ x, |f x| ≤ C) (n : ℕ) :
    |stoppedSum f T t n| ≤ C * min t T := by
  by_cases hn : n = 0
  · subst n
    simp only [stoppedSum, Finset.range_zero, Finset.sum_empty, abs_zero]
    exact mul_nonneg ((abs_nonneg (f 0)).trans (hb 0)) (le_min ht hT)
  · rw [stoppedSum_eq_partitionSum hT]
    simpa only [stoppedPoint_zero T ht, stoppedPoint_end T t (Nat.pos_of_ne_zero hn), sub_zero]
      using abs_partitionSum_le (stoppedPoint_mono hT t n) n (fun i _ => hb _)

theorem tendsto_stoppedSum {f : ℝ → ℝ} (hf : Continuous f)
    {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) :
    Tendsto (stoppedSum f T t) atTop (𝓝 (∫ x in (0 : ℝ)..min t T, f x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (T + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Icc (0 : ℝ) T) hf.continuousOn
  obtain ⟨δ, hδ, hδmod⟩ := Metric.uniformContinuousOn_iff.mp hUC η hη
  have hwidth : Tendsto (fun n : ℕ => T / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, T / (n : ℝ) < δ := hwidth.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := (hev.and (eventually_ge_atTop 1)).exists_forall_of_atTop
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hmesh, hnpos⟩ := hN n hn
  have hn' : 0 < n := hnpos
  have hmem (i : ℕ) (hi : i ≤ n) : stoppedPoint T t n i ∈ Icc (0 : ℝ) T := by
    constructor
    · rw [← stoppedPoint_zero T ht n]
      exact stoppedPoint_mono hT t n (Nat.zero_le i)
    · exact (stoppedPoint_mono hT t n hi).trans
        ((stoppedPoint_end T t hn').le.trans (min_le_right t T))
  have he := partition_error_le hf (stoppedPoint_mono hT t n) n (ε := η) ?_
  · rw [stoppedPoint_zero T ht, stoppedPoint_end T t hn',
      ← stoppedSum_eq_partitionSum hT] at he
    change |stoppedSum f T t n - ∫ x in (0 : ℝ)..min t T, f x| < ε
    calc
      _ ≤ η * (min t T - 0) := he
      _ ≤ η * T := by gcongr; simp
      _ < ε := by
        dsimp [η]
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ (by linarith : 0 < T + 1)).mpr
        nlinarith
  · intro i hi x hx
    have hleft := hmem i hi.le
    have hright := hmem (i + 1) (Nat.succ_le_of_lt hi)
    have hxT : x ∈ Icc (0 : ℝ) T := ⟨hleft.1.trans hx.1, hx.2.trans hright.2⟩
    have hdist : dist (stoppedPoint T t n i) x < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.1)]
      have hstep := stoppedPoint_step_le hT t n i
      linarith [hx.2]
    exact (hδmod _ hleft x hxT hdist).le

theorem tendsto_stoppedSum_L1
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℝ → Ω → ℝ} (hm : ∀ t, AEStronglyMeasurable (H t) μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => H t ω))
    {C T t : ℝ} (hb : ∀ᵐ ω ∂μ, ∀ s, |H s ω| ≤ C)
    (hT : 0 ≤ T) (ht : 0 ≤ t) :
    Tendsto (fun n => eLpNorm
      ((fun ω => stoppedSum (fun s => H s ω) T t n) -
        (fun ω => ∫ s in (0 : ℝ)..min t T, H s ω)) 1 μ) atTop (𝓝 0) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun ω => stoppedSum (fun s => H s ω) T t n) μ := by
    unfold stoppedSum
    apply Finset.aestronglyMeasurable_fun_sum
    intro i hi
    exact (hm _).const_mul _
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ,
      ‖stoppedSum (fun s => H s ω) T t n‖ ≤ C * min t T := by
    filter_upwards [hb] with ω hω
    exact abs_stoppedSum_le hT ht hω n
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => stoppedSum (fun s => H s ω) T t n)
      atTop (𝓝 (∫ s in (0 : ℝ)..min t T, H s ω)) := by
    filter_upwards [hc] with ω hω
    exact tendsto_stoppedSum hω hT ht
  have h := tendsto_lintegral_norm_of_dominated_convergence hmeas
    (integrable_const (C * min t T)).hasFiniteIntegral hbound hlim
  have hlimitMeas := aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim
  simpa only [eLpNorm_one_eq_lintegral_enorm ((hmeas _).sub hlimitMeas),
    Pi.sub_apply, ← ofReal_norm] using h

theorem tendsto_stoppedSquareSum_L1
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℝ → Ω → ℝ} (hm : ∀ t, AEStronglyMeasurable (H t) μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => H t ω))
    {C T t : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂μ, ∀ s, |H s ω| ≤ C)
    (hT : 0 ≤ T) (ht : 0 ≤ t) :
    Tendsto (fun n => eLpNorm
      ((fun ω => stoppedSum (fun s => (H s ω) ^ 2) T t n) -
        (fun ω => ∫ s in (0 : ℝ)..min t T, (H s ω) ^ 2)) 1 μ) atTop (𝓝 0) := by
  apply tendsto_stoppedSum_L1 (fun t => (hm t).pow 2)
    (hc.mono (fun ω hω => hω.pow 2)) (C := C ^ 2) _ hT ht
  filter_upwards [hb] with ω hω
  intro s
  simpa only [Pi.pow_apply, abs_sq, sq_abs] using
    (sq_le_sq₀ (abs_nonneg (H s ω)) hC).mpr (hω s)

theorem tendsto_stoppedSquareSum_L1_nnreal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℝ≥0 → Ω → ℝ} (hm : ∀ t, AEStronglyMeasurable (H t) μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂μ, ∀ s, |H s ω| ≤ C)
    (T t : ℝ≥0) :
    Tendsto (fun n => eLpNorm
      ((fun ω => stoppedSum (fun s => (H s.toNNReal ω) ^ 2) T t n) -
        (fun ω => ∫ s in (0 : ℝ)..min (t : ℝ) T, (H s.toNNReal ω) ^ 2)) 1 μ)
      atTop (𝓝 0) := by
  apply tendsto_stoppedSquareSum_L1 (fun s => hm s.toNNReal) _ hC _ T.coe_nonneg t.coe_nonneg
  · filter_upwards [hc] with ω hω
    exact hω.comp (by fun_prop)
  · filter_upwards [hb] with ω hω
    exact fun s => hω s.toNNReal

end Problem367.RandomRiemann

end

end OAI
