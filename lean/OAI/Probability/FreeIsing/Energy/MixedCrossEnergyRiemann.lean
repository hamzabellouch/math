import OAI.Probability.FreeIsing.Energy.CrossEnergyRiemann

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators
namespace Problem367.CrossEnergyRiemann
open EnergyRiemann

theorem error_le_of_integrable {f : ℝ → ℝ → ℝ}
    (hsec : ∀ s a b, IntervalIntegrable (f s) volume a b)
    (hdiag : ∀ a b, IntervalIntegrable (fun r => f r r) volume a b)
    {T ε : ℝ} (hT : 0 ≤ T) {n : ℕ} (hn : 0 < n)
    (hmod : ∀ i < n, ∀ r ∈ Icc (point T n i) (point T n (i + 1)),
      |f (point T n i) r - f r r| ≤ ε) :
    |sum f T n - ∫ r in (0 : ℝ)..T, f r r| ≤ ε * T := by
  have hpart := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := point T n) (n := n) (fun i _ => hdiag _ _)
  rw [point_zero, point_end T hn] at hpart
  have heq : sum f T n - (∫ r in (0 : ℝ)..T, f r r) =
      ∑ i ∈ Finset.range n, ∫ r in point T n i..point T n (i + 1),
        f (point T n i) r - f r r := by
    rw [sum, ← hpart, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact (intervalIntegral.integral_sub (hsec _ _ _)
      (hdiag _ _)).symm
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

theorem tendsto_sum_of_first_uniform {f : ℝ → ℝ → ℝ}
    (hsec : ∀ s a b, IntervalIntegrable (f s) volume a b)
    (hdiag : ∀ a b, IntervalIntegrable (fun r => f r r) volume a b)
    {T : ℝ} (hT : 0 ≤ T)
    (huniform : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist s t < δ → |f s t - f t t| ≤ ε) :
    Tendsto (sum f T) atTop (𝓝 (∫ r in (0 : ℝ)..T, f r r)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (T + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := huniform η hη
  have hw : Tendsto (fun n : ℕ => T / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := ((hw.eventually (gt_mem_nhds hδ)).and
    (eventually_ge_atTop 1)).exists_forall_of_atTop
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hnδ, hnpos⟩ := hN n hn
  have he := error_le_of_integrable hsec hdiag hT (show 0 < n from hnpos) (ε := η) ?_
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
    exact hmod _ hl r hrT hdist

theorem intervalIntegrable_crossMoment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {H K : ℝ → Ω → ℝ}
    (hH : Measurable (Function.uncurry H)) (hK : Measurable (Function.uncurry K))
    {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hbH : ∀ t ω, |H t ω| ≤ A) (hbK : ∀ t ω, |K t ω| ≤ B)
    (a b : ℝ) : IntervalIntegrable (fun t => ∫ ω, H t ω * K t ω ∂P) volume a b := by
  let : IsFiniteMeasure (volume.restrict (uIoc a b)) :=
    isFiniteMeasure_restrict.mpr (by exact measure_Ioc_lt_top.ne)
  have hi : Integrable (fun p : ℝ × Ω => H p.1 p.2 * K p.1 p.2)
      ((volume.restrict (uIoc a b)).prod P) := by
    apply (integrable_const (A * B)).mono' (hH.mul hK).aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      change ‖H p.1 p.2 * K p.1 p.2‖ ≤ A * B
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hbH p.1 p.2) (hbK p.1 p.2) (abs_nonneg _) hA
  exact intervalIntegrable_iff.mpr hi.integral_prod_left

theorem tendsto_sum_mixed_crossMoment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {H K : ℝ → Ω → ℝ}
    (hH : ∀ t, Measurable (H t)) (hcH : ∀ ω, Continuous (fun t => H t ω))
    (hK : Measurable (Function.uncurry K))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbH : ∀ t ω, |H t ω| ≤ A) (hbK : ∀ t ω, |K t ω| ≤ B)
    {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (sum (fun s t => ∫ ω, H s ω * K t ω ∂P) T) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, ∫ ω, H t ω * K t ω ∂P)) := by
  have hmH : Measurable (Function.uncurry H) :=
    measurable_uncurry_of_continuous_of_measurable hcH hH
  have hmK (t : ℝ) : Measurable (K t) :=
    hK.comp (measurable_const.prodMk measurable_id)
  have hint (s t : ℝ) : Integrable (fun ω => H s ω * K t ω) P := by
    apply (integrable_const (A * B)).mono' ((hH s).mul (hmK t)).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      change ‖H s ω * K t ω‖ ≤ A * B
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hbH s ω) (hbK t ω) (abs_nonneg _) hA
  let g : ℝ × ℝ → ℝ := fun p => ∫ ω, |H p.1 ω - H p.2 ω| ∂P
  have hg : Continuous g := by
    apply continuous_of_dominated (bound := fun _ => 2 * A)
    · intro p
      exact ((hH p.1).sub (hH p.2)).abs.aestronglyMeasurable
    · intro p
      exact Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_abs]
        exact (abs_sub _ _).trans (by linarith [hbH p.1 ω, hbH p.2 ω])
    · exact integrable_const _
    · exact Eventually.of_forall fun ω =>
        (((hcH ω).comp continuous_fst).sub ((hcH ω).comp continuous_snd)).abs
  apply tendsto_sum_of_first_uniform
  · intro s a b
    exact intervalIntegrable_crossMoment (H := fun _ ω => H s ω) ((hH s).comp measurable_snd) hK hA hB
      (fun _ ω => hbH s ω) hbK a b
  · exact intervalIntegrable_crossMoment hmH hK hA hB hbH hbK
  · exact hT
  · intro ε hε
    have hη : 0 < ε / (B + 1) := div_pos hε (by linarith)
    have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
      (s := (Icc (0 : ℝ) T) ×ˢ (Icc (0 : ℝ) T)) hg.continuousOn
    obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / (B + 1)) hη
    refine ⟨δ, hδ, ?_⟩
    intro s hs t ht hst
    have hpdist : dist (s, t) (t, t) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hst
    have hsmall := hmod (s, t) ⟨hs, ht⟩ (t, t) ⟨ht, ht⟩ hpdist
    have hg0 : g (t, t) = 0 := by simp [g]
    rw [hg0, dist_zero_right, Real.norm_eq_abs] at hsmall
    have hgpos : 0 ≤ g (s, t) := integral_nonneg fun _ => abs_nonneg _
    rw [abs_of_nonneg hgpos] at hsmall
    calc
      _ = |∫ ω, (H s ω - H t ω) * K t ω ∂P| := by
        rw [← integral_sub (hint s t) (hint t t)]
        congr 2
        funext ω
        ring
      _ ≤ ∫ ω, |(H s ω - H t ω) * K t ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, |H s ω - H t ω| * B ∂P := by
        apply integral_mono
        · have hsub : Integrable (fun ω => (H s ω - H t ω) * K t ω) P := by
            apply ((hint s t).sub (hint t t)).congr
            filter_upwards with ω
            change H s ω * K t ω - H t ω * K t ω = (H s ω - H t ω) * K t ω
            ring
          exact hsub.abs
        · apply (integrable_const (2 * A * B)).mono'
            (((hH s).sub (hH t)).abs.mul measurable_const).aestronglyMeasurable
          exact Eventually.of_forall fun ω => by
            change ‖|H s ω - H t ω| * B‖ ≤ 2 * A * B
            rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hB]
            exact mul_le_mul_of_nonneg_right
              ((abs_sub _ _).trans (by linarith [hbH s ω, hbH t ω])) hB
        · intro ω
          change |(H s ω - H t ω) * K t ω| ≤ |H s ω - H t ω| * B
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hbK t ω) (abs_nonneg _)
      _ = g (s, t) * B := by rw [integral_mul_const]
      _ ≤ (ε / (B + 1)) * B := mul_le_mul_of_nonneg_right hsmall.le hB
      _ ≤ ε := by
        rw [div_mul_eq_mul_div]
        exact (div_le_iff₀ (by linarith : 0 < B + 1)).mpr (by nlinarith)

theorem tendsto_mixed_cross_energy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {H K : ℝ≥0 → Ω → ℝ}
    (hH : ∀ t, Measurable (H t)) (hcH : ∀ ω, Continuous (fun t => H t ω))
    (hK : Measurable (Function.uncurry K))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbH : ∀ t ω, |H t ω| ≤ A) (hbK : ∀ t ω, |K t ω| ≤ B)
    (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      ∫ r in (BrownianGrid.uniformGrid T n i : ℝ)..(BrownianGrid.uniformGrid T n (i + 1) : ℝ),
        ∫ ω, H (BrownianGrid.uniformGrid T n i) ω * K r.toNNReal ω ∂P)
      atTop (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ ω, H r.toNNReal ω * K r.toNNReal ω ∂P)) := by
  have hp (n i : ℕ) : point (T : ℝ) n i = (BrownianGrid.uniformGrid T n i : ℝ) := by
    simp only [point, BrownianGrid.uniformGrid, NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_natCast]
    ring
  have hl := tendsto_sum_mixed_crossMoment (P := P)
    (H := fun r => H r.toNNReal) (K := fun r => K r.toNNReal)
    (fun r => hH r.toNNReal)
    (fun ω => (hcH ω).comp (by fun_prop))
    (hK.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
    hA hB (fun r ω => hbH r.toNNReal ω) (fun r ω => hbK r.toNNReal ω) T.coe_nonneg
  change Tendsto (fun n => CrossEnergyRiemann.sum
    (fun (s t : ℝ) => ∫ ω, H s.toNNReal ω * K t.toNNReal ω ∂P) (T : ℝ) n)
    atTop (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ ω, H r.toNNReal ω * K r.toNNReal ω ∂P)) at hl
  simpa only [CrossEnergyRiemann.sum, hp, Real.toNNReal_coe] using hl

end Problem367.CrossEnergyRiemann

end

end OAI
