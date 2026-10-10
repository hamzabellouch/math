import OAI.Probability.FreeIsing.Energy.EnergyRiemannApproximation

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators

namespace Problem367.EnergyRiemann

def stoppedSum (f : ℝ → ℝ) (T U : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    (min U (point T n (i + 1)) - min U (point T n i)) * f (point T n i)

theorem capped_point_step_le {T U : ℝ} (hT : 0 ≤ T) (n i : ℕ) :
    min U (point T n (i + 1)) - min U (point T n i) ≤ T / n := by
  have hle := point_mono hT n (Nat.le_succ i)
  have hstep := point_step T n i
  by_cases hU : U ≤ point T n i
  · rw [min_eq_left hU, min_eq_left (hU.trans hle), sub_self]
    positivity
  · rw [min_eq_right (le_of_not_ge hU)]
    linarith [min_le_right U (point T n (i + 1))]

theorem stopped_error_le {f : ℝ → ℝ} (hf : Continuous f) {T U ε : ℝ}
    (hT : 0 ≤ T) (hU : 0 ≤ U) (hε : 0 ≤ ε) {n : ℕ} (hn : 0 < n)
    (hmod : ∀ i < n, ∀ x ∈ Icc (point T n i) (point T n (i + 1)),
      |f (point T n i) - f x| ≤ ε) :
    |stoppedSum f T U n - ∫ x in (0 : ℝ)..min U T, f x| ≤ ε * T := by
  let a : ℕ → ℝ := fun i => min U (point T n i)
  have hpart := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := a) (n := n) (fun i _ => hf.intervalIntegrable _ _)
  have ha0 : a 0 = 0 := by simp only [a, point_zero, min_eq_right hU]
  have han : a n = min U T := by
    dsimp only [a]
    rw [point_end T hn]
  rw [ha0, han] at hpart
  have hcluster (i : ℕ) :
      (a (i + 1) - a i) * f (point T n i) - (∫ x in a i..a (i + 1), f x) =
        ∫ x in a i..a (i + 1), f (point T n i) - f x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul]
  have hdecomp : stoppedSum f T U n - (∫ x in (0 : ℝ)..min U T, f x) =
      ∑ i ∈ Finset.range n, ∫ x in a i..a (i + 1), f (point T n i) - f x := by
    rw [stoppedSum, ← hpart, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => hcluster i)
  rw [hdecomp]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |∫ x in a i..a (i + 1), f (point T n i) - f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, ε * (T / n) := by
      apply Finset.sum_le_sum
      intro i hi
      have hle : a i ≤ a (i + 1) := min_le_min_left U (point_mono hT n (Nat.le_succ i))
      have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := a i) (b := a (i + 1)) (C := ε)
        (f := fun x => f (point T n i) - f x) (fun x hx => ?_)
      · have hb : |∫ x in a i..a (i + 1), f (point T n i) - f x| ≤
            ε * (a (i + 1) - a i) := by
          simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)] using hbound
        exact hb.trans (mul_le_mul_of_nonneg_left (capped_point_step_le hT n i) hε)
      · rw [uIoc_of_le hle] at hx
        by_cases hUi : U ≤ point T n i
        · have hai : a i = U := min_eq_left hUi
          have hau : a (i + 1) ≤ U := min_le_left _ _
          exact False.elim (not_lt_of_ge (hx.2.trans hau) (by simpa only [hai] using hx.1))
        · have hai : a i = point T n i := min_eq_right (le_of_not_ge hUi)
          exact hmod i (Finset.mem_range.mp hi) x
            ⟨by simpa only [hai] using hx.1.le, hx.2.trans (min_le_right _ _)⟩
    _ = ε * T := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      field_simp

theorem tendsto_stoppedSum {f : ℝ → ℝ} (hf : Continuous f) {T U : ℝ}
    (hT : 0 ≤ T) (hU : 0 ≤ U) :
    Tendsto (stoppedSum f T U) atTop (𝓝 (∫ x in (0 : ℝ)..min U T, f x)) := by
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
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hmesh, hnpos⟩ := hN n hn
  have he := stopped_error_le hf hT hU hη.le hnpos (ε := η) ?_
  · change |stoppedSum f T U n - ∫ x in (0 : ℝ)..min U T, f x| < ε
    apply he.trans_lt
    change ε / (T + 1) * T < ε
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < T + 1)).mpr
    nlinarith
  · intro i hi x hx
    have hleft := point_mem hT hnpos hi.le
    have hright := point_mem hT hnpos (Nat.succ_le_of_lt hi)
    have hxT : x ∈ Icc (0 : ℝ) T := ⟨hleft.1.trans hx.1, hx.2.trans hright.2⟩
    have hdist : dist (point T n i) x < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.1)]
      have hstep := point_step T n i
      linarith [hx.2]
    exact (hδmod _ hleft x hxT hdist).le

theorem tendsto_stopped_energy_sum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (H t) P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T t : ℝ≥0) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      (((min t (((i + 1 : ℕ) : ℝ≥0) * T / n) : ℝ≥0) : ℝ) -
        ((min t ((i : ℝ≥0) * T / n) : ℝ≥0) : ℝ)) *
          ∫ ω, (H ((i : ℝ≥0) * T / n) ω) ^ 2 ∂P)
      atTop (𝓝 (∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ),
        ∫ ω, (H s.toNNReal ω) ^ 2 ∂P)) := by
  have hcont : Continuous (fun s : ℝ => energy P H s.toNNReal) :=
    (continuous_energy hm hc hC hb).comp (by fun_prop)
  have hlim := tendsto_stoppedSum hcont T.coe_nonneg t.coe_nonneg
  have hpoint (n i : ℕ) : point (T : ℝ) n i = (((i : ℝ≥0) * T / n : ℝ≥0) : ℝ) := by
    simp only [point, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
    ring
  convert hlim using 1
  funext n
  unfold stoppedSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [hpoint n i, hpoint n (i + 1)]
  simp only [NNReal.coe_min, Real.toNNReal_coe, energy]
  all_goals simp only [NNReal.coe_min, energy]

end Problem367.EnergyRiemann

end

end OAI
