import OAI.Probability.FreeIsing.Brownian.UniformGrid
import OAI.Probability.FreeIsing.Energy.EnergyRiemannApproximation

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators

namespace Problem367.CrossEnergyRiemann

open EnergyRiemann

def sum (f : ℝ → ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    ∫ r in point T n i..point T n (i + 1), f (point T n i) r

theorem error_le {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f))
    {T ε : ℝ} (hT : 0 ≤ T) {n : ℕ} (hn : 0 < n)
    (hmod : ∀ i < n, ∀ r ∈ Icc (point T n i) (point T n (i + 1)),
      |f (point T n i) r - f r r| ≤ ε) :
    |sum f T n - ∫ r in (0 : ℝ)..T, f r r| ≤ ε * T := by
  have hd : Continuous (fun r => f r r) := hf.comp (continuous_id.prodMk continuous_id)
  have hs (x : ℝ) : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
  have hpart := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := point T n) (n := n) (fun i _ => hd.intervalIntegrable _ _)
  rw [point_zero, point_end T hn] at hpart
  have heq : sum f T n - (∫ r in (0 : ℝ)..T, f r r) =
      ∑ i ∈ Finset.range n, ∫ r in point T n i..point T n (i + 1),
        f (point T n i) r - f r r := by
    rw [sum, ← hpart, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact (intervalIntegral.integral_sub ((hs _).intervalIntegrable _ _)
      (hd.intervalIntegrable _ _)).symm
  rw [heq]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |∫ r in point T n i..point T n (i + 1), f (point T n i) r - f r r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, ε * (T / n) := by
      apply Finset.sum_le_sum
      intro i hi
      have hle := point_mono hT n (Nat.le_succ i)
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := point T n i) (b := point T n (i + 1)) (C := ε)
        (f := fun r => f (point T n i) r - f r r) (fun r hr => ?_)
      · simpa only [Real.norm_eq_abs, point_step,
          abs_of_nonneg (div_nonneg hT (Nat.cast_nonneg n))] using hb
      · rw [uIoc_of_le hle] at hr
        exact hmod i (Finset.mem_range.mp hi) r ⟨hr.1.le, hr.2⟩
    _ = ε * T := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      field_simp

theorem tendsto_sum {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f))
    {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (sum f T) atTop (𝓝 (∫ r in (0 : ℝ)..T, f r r)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (T + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (s := (Icc (0 : ℝ) T) ×ˢ (Icc (0 : ℝ) T)) hf.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  have hw : Tendsto (fun n : ℕ => T / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := ((hw.eventually (gt_mem_nhds hδ)).and
    (eventually_ge_atTop 1)).exists_forall_of_atTop
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hnδ, hnpos⟩ := hN n hn
  have he := error_le hf hT (show 0 < n from hnpos) (ε := η) ?_
  · change |sum f T n - ∫ r in (0 : ℝ)..T, f r r| < ε
    apply he.trans_lt
    change ε / (T + 1) * T < ε
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < T + 1)).mpr
    nlinarith
  · intro i hi r hr
    have hl := point_mem hT hnpos hi.le
    have hh := point_mem hT hnpos (Nat.succ_le_of_lt hi)
    have hrT : r ∈ Icc (0 : ℝ) T := ⟨hl.1.trans hr.1, hr.2.trans hh.2⟩
    have hdist : dist (point T n i) r < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hr.1)]
      have hstep := point_step T n i
      linarith [hr.2]
    have hpdist : dist (point T n i, r) (r, r) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hdist
    exact (hmod _ ⟨hl, hrT⟩ _ ⟨hrT, hrT⟩ hpdist).le

theorem continuous_crossMoment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (H t) P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => ∫ ω, H p.1 ω * H p.2 ω ∂P) := by
  apply continuous_of_dominated (bound := fun _ => C ^ 2)
  · intro p
    exact (hm p.1).mul (hm p.2)
  · intro p
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_mul, pow_two]
    exact mul_le_mul (hω p.1) (hω p.2) (abs_nonneg _) hC
  · exact integrable_const _
  · filter_upwards [hc] with ω hω
    exact (hω.comp continuous_fst).mul (hω.comp continuous_snd)

theorem tendsto_cross_energy {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (H t) P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      ∫ r in (BrownianGrid.uniformGrid T n i : ℝ)..(BrownianGrid.uniformGrid T n (i + 1) : ℝ),
        ∫ ω, H (BrownianGrid.uniformGrid T n i) ω * H r.toNNReal ω ∂P)
      atTop (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ ω, H r.toNNReal ω ^ 2 ∂P)) := by
  have hcont : Continuous (fun p : ℝ × ℝ =>
      ∫ ω, H p.1.toNNReal ω * H p.2.toNNReal ω ∂P) :=
    (continuous_crossMoment hm hc hC hb).comp
      (show Continuous (fun p : ℝ × ℝ => (p.1.toNNReal, p.2.toNNReal)) by fun_prop)
  have hp (n i : ℕ) : point (T : ℝ) n i = (BrownianGrid.uniformGrid T n i : ℝ) := by
    simp only [point, BrownianGrid.uniformGrid, NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_natCast]
    ring
  have hl := tendsto_sum (f := fun (s t : ℝ) =>
    ∫ ω, H s.toNNReal ω * H t.toNNReal ω ∂P) hcont T.coe_nonneg
  change Tendsto (fun n => CrossEnergyRiemann.sum
    (fun (s t : ℝ) => ∫ ω, H s.toNNReal ω * H t.toNNReal ω ∂P) (T : ℝ) n)
    atTop (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ ω, H r.toNNReal ω * H r.toNNReal ω ∂P)) at hl
  simpa only [CrossEnergyRiemann.sum, hp, Real.toNNReal_coe, pow_two] using hl

end Problem367.CrossEnergyRiemann

end

end OAI
