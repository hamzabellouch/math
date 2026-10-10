import OAI.Probability.FreeIsing.Energy.EnergyRiemannApproximation

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace Problem367.WeightedPrimitiveApproximation

open EnergyRiemann (point point_zero point_end point_step point_mono point_mem)

def weightedSum (f a : ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, f (point T n i) *
    ∫ s in point T n i..point T n (i + 1), a s

lemma cell_subset {T : ℝ} (hT : 0 ≤ T) {n i : ℕ}
    (hn : 0 < n) (hi : i < n) :
    uIcc (point T n i) (point T n (i + 1)) ⊆ uIcc (0 : ℝ) T := by
  rw [uIcc_of_le hT]
  exact uIcc_subset_Icc (point_mem hT hn hi.le) (point_mem hT hn hi)

theorem error_le {f a : ℝ → ℝ} {T ε : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (ha : IntervalIntegrable a volume 0 T)
    {n : ℕ} (hn : 0 < n)
    (hmod : ∀ i < n, ∀ s ∈ Icc (point T n i) (point T n (i + 1)),
      |f (point T n i) - f s| ≤ ε) :
    |weightedSum f a T n - ∫ s in (0 : ℝ)..T, f s * a s| ≤
      ε * ∫ s in (0 : ℝ)..T, |a s| := by
  have hfa : IntervalIntegrable (fun s => f s * a s) volume 0 T := by
    simpa only [mul_comm, uIcc_of_le hT] using ha.mul_continuousOn
      (show ContinuousOn f (uIcc 0 T) by simpa only [uIcc_of_le hT] using hf)
  have hcellA (i : ℕ) (hi : i < n) := ha.mono_set (cell_subset hT hn hi)
  have hcellFA (i : ℕ) (hi : i < n) := hfa.mono_set (cell_subset hT hn hi)
  have hpart := intervalIntegral.sum_integral_adjacent_intervals hcellFA
  rw [point_zero, point_end T hn] at hpart
  have hpartAbs := intervalIntegral.sum_integral_adjacent_intervals
    (fun i hi => (hcellA i hi).abs)
  rw [point_zero, point_end T hn] at hpartAbs
  have hdecomp : weightedSum f a T n - (∫ s in (0 : ℝ)..T, f s * a s) =
      ∑ i ∈ Finset.range n, ∫ s in point T n i..point T n (i + 1),
        (f (point T n i) - f s) * a s := by
    rw [weightedSum, ← hpart, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (fun s => (f (point T n i) - f s) * a s) =
        (fun s => f (point T n i) * a s - f s * a s) by funext s; ring]
    rw [intervalIntegral.integral_sub ((hcellA i (Finset.mem_range.mp hi)).const_mul _)
      (hcellFA i (Finset.mem_range.mp hi)), intervalIntegral.integral_const_mul]
  rw [hdecomp]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |∫ s in point T n i..point T n (i + 1), (f (point T n i) - f s) * a s| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n,
        ε * ∫ s in point T n i..point T n (i + 1), |a s| := by
      apply Finset.sum_le_sum
      intro i hi
      have hin := Finset.mem_range.mp hi
      have hle := point_mono hT n (Nat.le_succ i)
      have hdiff : IntervalIntegrable
          (fun s => (f (point T n i) - f s) * a s) volume
          (point T n i) (point T n (i + 1)) := by
        simpa only [sub_mul] using
          ((hcellA i hin).const_mul (f (point T n i))).sub (hcellFA i hin)
      calc
        _ ≤ ∫ s in point T n i..point T n (i + 1),
            |(f (point T n i) - f s) * a s| := by
          simpa only [Real.norm_eq_abs] using
            (intervalIntegral.norm_integral_le_integral_norm (f := fun s =>
              (f (point T n i) - f s) * a s) hle)
        _ ≤ ∫ s in point T n i..point T n (i + 1), ε * |a s| := by
          apply intervalIntegral.integral_mono_on hle hdiff.abs ((hcellA i hin).abs.const_mul ε)
          intro s hs
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hmod i hin s hs) (abs_nonneg _)
        _ = _ := intervalIntegral.integral_const_mul _ _
    _ = _ := by rw [← Finset.mul_sum, hpartAbs]

theorem tendsto_weightedSum {f a : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (ha : IntervalIntegrable a volume 0 T) :
    Tendsto (weightedSum f a T) atTop (𝓝 (∫ s in (0 : ℝ)..T, f s * a s)) := by
  have hmass : 0 ≤ ∫ s in (0 : ℝ)..T, |a s| :=
    intervalIntegral.integral_nonneg hT (fun _ _ => abs_nonneg _)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / ((∫ s in (0 : ℝ)..T, |a s|) + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, hδmod⟩ := Metric.uniformContinuousOn_iff.mp hUC η hη
  have hwidth : Tendsto (fun n : ℕ => T / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := ((hwidth.eventually (gt_mem_nhds hδ)).and
    (eventually_ge_atTop 1)).exists_forall_of_atTop
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hmesh, hnpos⟩ := hN n hn
  have hn' : 0 < n := hnpos
  have he := error_le hT hf ha hn' (ε := η) ?_
  · change |weightedSum f a T n - ∫ s in (0 : ℝ)..T, f s * a s| < ε
    apply he.trans_lt
    change ε / ((∫ s in (0 : ℝ)..T, |a s|) + 1) *
      (∫ s in (0 : ℝ)..T, |a s|) < ε
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < (∫ s in (0 : ℝ)..T, |a s|) + 1)).mpr
    nlinarith
  · intro i hi s hs
    have hleft := point_mem hT hn' hi.le
    have hright := point_mem hT hn' hi
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hleft.1.trans hs.1, hs.2.trans hright.2⟩
    have hd : dist (point T n i) s < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.1)]
      have hstep := point_step T n i
      linarith [hs.2]
    exact (hδmod _ hleft s hsT hd).le

theorem weightedSum_eq_primitiveSum {f a : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T) {n : ℕ} (hn : 0 < n) :
    weightedSum f a T n = ∑ i ∈ Finset.range n, f (point T n i) *
      ((∫ s in (0 : ℝ)..point T n (i + 1), a s) -
        ∫ s in (0 : ℝ)..point T n i, a s) := by
  apply Finset.sum_congr rfl
  intro i hi
  have hin := Finset.mem_range.mp hi
  have h0i : IntervalIntegrable a volume 0 (point T n i) := by
    apply ha.mono_set
    rw [uIcc_of_le hT]
    exact uIcc_subset_Icc ⟨le_rfl, hT⟩ (point_mem hT hn hin.le)
  have hcell := ha.mono_set (cell_subset hT hn hin)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0i hcell
  congr 1
  linarith [hadd]

theorem tendsto_primitiveSum {f a : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (ha : IntervalIntegrable a volume 0 T) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, f (point T n i) *
      ((∫ s in (0 : ℝ)..point T n (i + 1), a s) -
        ∫ s in (0 : ℝ)..point T n i, a s)) atTop
      (𝓝 (∫ s in (0 : ℝ)..T, f s * a s)) := by
  apply (tendsto_weightedSum hT hf ha).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact weightedSum_eq_primitiveSum hT ha hn

lemma abs_integral_mul_le {f a : ℝ → ℝ} {T K : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (ha : IntervalIntegrable a volume 0 T)
    (hb : ∀ s ∈ Icc 0 T, |f s| ≤ K) :
    |∫ s in (0 : ℝ)..T, f s * a s| ≤ K * ∫ s in (0 : ℝ)..T, |a s| := by
  have hfa : IntervalIntegrable (fun s => f s * a s) volume 0 T := by
    simpa only [mul_comm] using ha.mul_continuousOn
      (show ContinuousOn f (uIcc 0 T) by simpa only [uIcc_of_le hT] using hf)
  calc
    _ ≤ ∫ s in (0 : ℝ)..T, |f s * a s| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm (f := fun s => f s * a s) hT)
    _ ≤ ∫ s in (0 : ℝ)..T, K * |a s| := by
      apply intervalIntegral.integral_mono_on hT hfa.abs (ha.abs.const_mul K)
      intro s hs
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb s hs) (abs_nonneg _)
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem error_le_two_mul_mass {f a : ℝ → ℝ} {T K : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (ha : IntervalIntegrable a volume 0 T)
    (hK : 0 ≤ K) (hb : ∀ s ∈ Icc 0 T, |f s| ≤ K) (n : ℕ) :
    |weightedSum f a T n - ∫ s in (0 : ℝ)..T, f s * a s| ≤
      (2 * K) * ∫ s in (0 : ℝ)..T, |a s| := by
  by_cases hn : n = 0
  · subst n
    simp only [weightedSum, Finset.range_zero, Finset.sum_empty, zero_sub, abs_neg]
    have hmass : 0 ≤ ∫ s in (0 : ℝ)..T, |a s| :=
      intervalIntegral.integral_nonneg hT (fun _ _ => abs_nonneg _)
    exact (abs_integral_mul_le hT hf ha hb).trans
      (mul_le_mul_of_nonneg_right (by linarith : K ≤ 2 * K) hmass)
  · have hn' := Nat.pos_of_ne_zero hn
    apply error_le hT hf ha hn'
    intro i hi s hs
    have hl := point_mem hT hn' hi.le
    have hr := point_mem hT hn' hi
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hl.1.trans hs.1, hs.2.trans hr.2⟩
    exact (abs_sub _ _).trans (by linarith [hb _ hl, hb s hsT])

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]

theorem integrable_weightedDensity {T K : ℝ} {f a : ℝ → Ω → ℝ}
    (hfm : Measurable (fun p : ℝ × Ω => f p.1 p.2))
    (ha : Integrable (fun p : ℝ × Ω => a p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hb : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, |f t ω| ≤ K) :
    Integrable (fun p : ℝ × Ω => f p.1 p.2 * a p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ) := by
  have hbp : ∀ᵐ p ∂(volume.restrict (Ioc 0 T)).prod μ, |f p.1 p.2| ≤ K := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hfm.abs measurable_const)).2
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hb.mono fun ω hω => hω t ⟨ht.1.le, ht.2⟩
  apply (ha.norm.const_mul K).mono' (hfm.aestronglyMeasurable.mul ha.aestronglyMeasurable)
  filter_upwards [hbp] with p hp
  simpa only [Real.norm_eq_abs, abs_mul, Pi.mul_apply] using
    mul_le_mul_of_nonneg_right hp (abs_nonneg (a p.1 p.2))

lemma integrable_cellIntegral {T : ℝ} (hT : 0 ≤ T) {a : ℝ → Ω → ℝ}
    (ha : Integrable (fun p : ℝ × Ω => a p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    {n i : ℕ} (hn : 0 < n) (hi : i < n) :
    Integrable (fun ω => ∫ s in point T n i..point T n (i + 1), a s ω) μ := by
  have hl := point_mem hT hn hi.le
  have hr := point_mem hT hn hi
  have hsub : Ioc (point T n i) (point T n (i + 1)) ⊆ Ioc (0 : ℝ) T := by
    intro s hs
    exact ⟨hl.1.trans_lt hs.1, hs.2.trans hr.2⟩
  have hc := ha.mono_measure (Measure.prod_mono
    (Measure.restrict_mono_set _ hsub) le_rfl)
  simpa only [intervalIntegral.integral_of_le (point_mono hT n (Nat.le_succ i))] using
    hc.integral_prod_right

theorem tendsto_integral_abs_error {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    {f a : ℝ → Ω → ℝ}
    (hfm : Measurable (fun p : ℝ × Ω => f p.1 p.2))
    (hf : ∀ᵐ ω ∂μ, ContinuousOn (fun t => f t ω) (Icc 0 T))
    (ha : Integrable (fun p : ℝ × Ω => a p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hb : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, |f t ω| ≤ K) :
    Tendsto (fun n => ∫ ω, |weightedSum (fun t => f t ω) (fun t => a t ω) T n -
      ∫ t in (0 : ℝ)..T, f t ω * a t ω| ∂μ) atTop (𝓝 0) := by
  have hPath : ∀ᵐ ω ∂μ, IntervalIntegrable (fun t => a t ω) volume 0 T :=
    ha.prod_left_ae.mono fun ω hω => (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hω
  have hmass : Integrable (fun ω => ∫ t in (0 : ℝ)..T, |a t ω|) μ := by
    simpa only [intervalIntegral.integral_of_le hT] using ha.abs.integral_prod_right
  have htarget : Integrable (fun ω => ∫ t in (0 : ℝ)..T, f t ω * a t ω) μ := by
    simpa only [intervalIntegral.integral_of_le hT] using
      (integrable_weightedDensity hfm ha hb).integral_prod_right
  have hsum (n : ℕ) : AEStronglyMeasurable
      (fun ω => weightedSum (fun t => f t ω) (fun t => a t ω) T n) μ := by
    unfold weightedSum
    apply Finset.aestronglyMeasurable_fun_sum
    intro i hi
    have hin := Finset.mem_range.mp hi
    have hn : 0 < n := (Nat.zero_le i).trans_lt hin
    exact ((hfm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mul
      (integrable_cellIntegral hT ha hn hin).aestronglyMeasurable
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun n ω => |weightedSum (fun t => f t ω) (fun t => a t ω) T n -
      ∫ t in (0 : ℝ)..T, f t ω * a t ω|) (f := fun _ => (0 : ℝ))
    (fun ω => (2 * K) * ∫ t in (0 : ℝ)..T, |a t ω|)
    (fun n => by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        ((hsum n).sub htarget.aestronglyMeasurable).norm)
    (hmass.const_mul (2 * K)) ?_ ?_
  · simpa only [integral_zero] using hlim
  · intro n
    filter_upwards [hf, hPath, hb] with ω hfω haω hbω
    simpa only [Real.norm_eq_abs, abs_abs] using error_le_two_mul_mass hT hfω haω hK hbω n
  · filter_upwards [hf, hPath] with ω hfω haω
    simpa only [sub_self, abs_zero] using
      ((tendsto_weightedSum hT hfω haω).sub
        (tendsto_const_nhds (x := ∫ t in (0 : ℝ)..T, f t ω * a t ω))).abs

theorem tendsto_integral_abs_compensator_error {T K : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) {f a A : ℝ → Ω → ℝ}
    (hfm : Measurable (fun p : ℝ × Ω => f p.1 p.2))
    (hf : ∀ᵐ ω ∂μ, ContinuousOn (fun t => f t ω) (Icc 0 T))
    (ha : Integrable (fun p : ℝ × Ω => a p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hb : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, |f t ω| ≤ K)
    (hA : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      A t ω = A 0 ω + ∫ s in (0 : ℝ)..t, a s ω) :
    Tendsto (fun n => ∫ ω,
      |(∑ i ∈ Finset.range n, f (point T n i) ω *
        (A (point T n (i + 1)) ω - A (point T n i) ω)) -
        ∫ t in (0 : ℝ)..T, f t ω * a t ω| ∂μ) atTop (𝓝 0) := by
  apply (tendsto_integral_abs_error hT hK hfm hf ha hb).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply integral_congr_ae
  filter_upwards [ha.prod_left_ae, hA] with ω haω hAω
  have hp := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 haω
  rw [weightedSum_eq_primitiveSum hT hp hn]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  have hin := Finset.mem_range.mp hi
  rw [hAω _ (point_mem hT hn hin), hAω _ (point_mem hT hn hin.le)]
  ring

end Probability

end Problem367.WeightedPrimitiveApproximation

end

end OAI
