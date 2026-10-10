import OAI.Probability.FreeIsing.Energy.DiscrepancyRowEnergy

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367.RowEnergyL1

private lemma abs_sq_sub_sq_le_young (x y : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    |x ^ 2 - y ^ 2| ≤ (1 + 1 / δ) * (x - y) ^ 2 + δ * y ^ 2 := by
  have ha : |x ^ 2 - y ^ 2| ≤ (x - y) ^ 2 + 2 * |x - y| * |y| := by
    calc
      _ = |(x - y) ^ 2 + 2 * (x - y) * y| := by congr 1; ring
      _ ≤ |(x - y) ^ 2| + |2 * (x - y) * y| := abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_mul]; norm_num
  have hsq := sq_nonneg (|x - y| - δ * |y|)
  rw [sub_sq, mul_pow, sq_abs, sq_abs] at hsq
  have hdiv : δ * (1 / δ) = 1 := mul_one_div_cancel hδ.ne'
  have hYoung : 2 * |x - y| * |y| ≤ (1 / δ) * (x - y) ^ 2 + δ * y ^ 2 := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    rw [mul_add, ← mul_assoc δ (1 / δ), hdiv, one_mul]
    nlinarith
  linarith

theorem abs_tsum_sq_sub_le {ι : Type*} {a b : ι → ℝ}
    (ha : Summable (fun i => (a i) ^ 2))
    (hb : Summable (fun i => (b i) ^ 2)) {δ : ℝ} (hδ : 0 < δ) :
    |(∑' i, (a i) ^ 2) - ∑' i, (b i) ^ 2| ≤
      (1 + 1 / δ) * (∑' i, (a i - b i) ^ 2) + δ * ∑' i, (b i) ^ 2 := by
  have hd := DiscrepancyEnergy.summable_sq_sub ha hb
  have habs : Summable (fun i => |(a i) ^ 2 - (b i) ^ 2|) := (ha.sub hb).abs
  rw [← ha.tsum_sub hb]
  calc
    |(∑' i, ((a i) ^ 2 - (b i) ^ 2))| ≤
        ∑' i, |(a i) ^ 2 - (b i) ^ 2| := by
      simpa only [Real.norm_eq_abs] using
        (norm_tsum_le_tsum_norm (f := fun i => (a i) ^ 2 - (b i) ^ 2)
          (by simpa only [Real.norm_eq_abs] using habs))
    _ ≤ ∑' i, ((1 + 1 / δ) * (a i - b i) ^ 2 + δ * (b i) ^ 2) :=
      habs.tsum_le_tsum (fun i => abs_sq_sub_sq_le_young (a i) (b i) hδ)
        ((hd.mul_left _).add (hb.mul_left _))
    _ = _ := by rw [Summable.tsum_add (hd.mul_left _) (hb.mul_left _),
      tsum_mul_left, tsum_mul_left]

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}

theorem tendsto_integral_abs_tsum_sq_sub
    {N : Type*} {l : Filter N} {a : N → ι → Ω → ℝ} {b : ι → Ω → ℝ}
    (ha : ∀ n i, MemLp (a n i) 2 μ) (hb : ∀ i, MemLp (b i) 2 μ)
    (haSum : ∀ n, Summable (fun i => ∫ ω, (a n i ω) ^ 2 ∂μ))
    (hbSum : Summable (fun i => ∫ ω, (b i ω) ^ 2 ∂μ))
    (hlim : Tendsto (fun n => ∑' i, ∫ ω, (a n i ω - b i ω) ^ 2 ∂μ)
      l (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |(∑' i, (a n i ω) ^ 2) - ∑' i, (b i ω) ^ 2| ∂μ)
      l (𝓝 0) := by
  have hA n := DiscrepancyEnergy.sq_row_integrable_of_summable_integrals
    (fun i => (ha n i).integrable_sq) (haSum n)
  have hB := DiscrepancyEnergy.sq_row_integrable_of_summable_integrals
    (fun i => (hb i).integrable_sq) hbSum
  have hD n := DiscrepancyEnergy.integrable_sq_difference_row
    (fun i => (ha n i).aestronglyMeasurable) (fun i => (hb i).aestronglyMeasurable)
    (hA n).2 hB.2 ((hA n).1.and hB.1)
  have hDsum n := DiscrepancyEnergy.hasSum_integral_sq_row
    (fun i => ((ha n i).sub (hb i)).aestronglyMeasurable)
    (((hA n).1.and hB.1).mono (fun ω hω =>
      DiscrepancyEnergy.summable_sq_sub hω.1 hω.2)) (hD n)
  have hDlim : Tendsto (fun n => ∫ ω, ∑' i, (a n i ω - b i ω) ^ 2 ∂μ) l (𝓝 0) := by
    have heq (n : N) : (∑' i, ∫ ω, (a n i ω - b i ω) ^ 2 ∂μ) =
        ∫ ω, ∑' i, (a n i ω - b i ω) ^ 2 ∂μ := by
      simpa only [Pi.sub_apply] using (hDsum n).tsum_eq
    simpa only [heq] using hlim
  let E : ℝ := ∫ ω, ∑' i, (b i ω) ^ 2 ∂μ
  have hE : 0 ≤ E := integral_nonneg (fun ω => tsum_nonneg (fun i => sq_nonneg _))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε / (2 * (E + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hcoef : 0 < 1 + 1 / δ := by positivity
  have hevent := hDlim.eventually (gt_mem_nhds
    (show 0 < ε / (2 * (1 + 1 / δ)) by positivity))
  filter_upwards [hevent] with n hn
  have hbound : (∫ ω, |(∑' i, (a n i ω) ^ 2) - ∑' i, (b i ω) ^ 2| ∂μ) ≤
      (1 + 1 / δ) * (∫ ω, ∑' i, (a n i ω - b i ω) ^ 2 ∂μ) + δ * E := by
    calc
      _ ≤ ∫ ω, (1 + 1 / δ) * (∑' i, (a n i ω - b i ω) ^ 2) +
          δ * (∑' i, (b i ω) ^ 2) ∂μ := by
        apply integral_mono_ae ((hA n).2.sub hB.2).abs
          (((hD n).const_mul _).add (hB.2.const_mul _))
        filter_upwards [(hA n).1, hB.1] with ω hω hω'
        exact abs_tsum_sq_sub_le hω hω' hδ
      _ = _ := by rw [integral_add ((hD n).const_mul _) (hB.2.const_mul _),
        integral_const_mul, integral_const_mul]
  have hfirst : (1 + 1 / δ) * (∫ ω, ∑' i, (a n i ω - b i ω) ^ 2 ∂μ) < ε / 2 := by
    have hh := (lt_div_iff₀ (show 0 < 2 * (1 + 1 / δ) by positivity)).mp hn
    nlinarith
  have hsecond : δ * E < ε / 2 := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (show 0 < 2 * (E + 1) by positivity)).mpr
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
  linarith

theorem tendsto_integral_abs_mul_sub
    {E : ℕ → Ω → ℝ} {F : Ω → ℝ} {m : ℕ → Ω → ℝ} {q : Ω → ℝ} {C : ℝ}
    (hE : ∀ n, Integrable (E n) μ) (hF : Integrable F μ)
    (hm : ∀ n, AEStronglyMeasurable (m n) μ) (hq : AEStronglyMeasurable q μ)
    (_hC : 0 ≤ C) (hmBound : ∀ n, ∀ᵐ ω ∂μ, |m n ω| ≤ C)
    (hqBound : ∀ᵐ ω ∂μ, |q ω| ≤ C)
    (hEconv : Tendsto (fun n => ∫ ω, |E n ω - F ω| ∂μ) atTop (𝓝 0))
    (hmconv : ∀ᵐ ω ∂μ, Tendsto (fun n => m n ω) atTop (𝓝 (q ω))) :
    Tendsto (fun n => ∫ ω, |m n ω * E n ω - q ω * F ω| ∂μ) atTop (𝓝 0) := by
  have hDiffBound (n : ℕ) : ∀ᵐ ω ∂μ, ‖m n ω - q ω‖ ≤ 2 * C := by
    filter_upwards [hmBound n, hqBound] with ω hω hω'
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith)
  have hDint (n : ℕ) : Integrable (fun ω => |(m n ω - q ω) * F ω|) μ :=
    (hF.bdd_mul ((hm n).sub hq) (hDiffBound n)).abs
  have hDlim : Tendsto (fun n => ∫ ω, |(m n ω - q ω) * F ω| ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun ω => (2 * C) * |F ω|)
      (fun n => (hDint n).aestronglyMeasurable) (hF.abs.const_mul (2 * C))
      (fun n => ?_) (f := fun _ => (0 : ℝ)) ?_
    · simpa using h
    · filter_upwards [hDiffBound n] with ω hω
      simpa only [Real.norm_eq_abs, abs_abs, abs_mul] using
        mul_le_mul_of_nonneg_right hω (abs_nonneg (F ω))
    · filter_upwards [hmconv] with ω hω
      simpa using ((hω.sub_const (q ω)).mul_const (F ω)).abs
  have hlim := (hEconv.const_mul C).add hDlim
  simp only [mul_zero, add_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => integral_nonneg (fun _ => abs_nonneg _))
  intro n
  have hmBoundNorm : ∀ᵐ ω ∂μ, ‖m n ω‖ ≤ C := by
    simpa only [Real.norm_eq_abs] using hmBound n
  have hqBoundNorm : ∀ᵐ ω ∂μ, ‖q ω‖ ≤ C := by
    simpa only [Real.norm_eq_abs] using hqBound
  have hfirstInt : Integrable (fun ω => C * |E n ω - F ω|) μ := by
    simpa only [Pi.sub_apply] using ((hE n).sub hF).abs.const_mul C
  calc
    _ ≤ ∫ ω, C * |E n ω - F ω| + |(m n ω - q ω) * F ω| ∂μ := by
      apply integral_mono_ae
        (((hE n).bdd_mul (hm n) hmBoundNorm).sub (hF.bdd_mul hq hqBoundNorm)).abs
        (hfirstInt.add (hDint n))
      filter_upwards [hmBound n] with ω hω
      change |m n ω * E n ω - q ω * F ω| ≤ _
      calc
        _ = |m n ω * (E n ω - F ω) + (m n ω - q ω) * F ω| := by
          congr 1
          ring
        _ ≤ |m n ω * (E n ω - F ω)| + |(m n ω - q ω) * F ω| := abs_add_le _ _
        _ ≤ _ := by
          rw [abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_right hω (abs_nonneg _)) le_rfl
    _ = _ := by rw [integral_add hfirstInt (hDint n),
      integral_const_mul]

theorem tendsto_integral_abs_multiplier_tsum_sq_sub
    {a : ℕ → ι → Ω → ℝ} {b : ι → Ω → ℝ}
    {m : ℕ → Ω → ℝ} {q : Ω → ℝ} {C : ℝ}
    (ha : ∀ n i, MemLp (a n i) 2 μ) (hb : ∀ i, MemLp (b i) 2 μ)
    (haSum : ∀ n, Summable (fun i => ∫ ω, (a n i ω) ^ 2 ∂μ))
    (hbSum : Summable (fun i => ∫ ω, (b i ω) ^ 2 ∂μ))
    (hlim : Tendsto (fun n => ∑' i, ∫ ω, (a n i ω - b i ω) ^ 2 ∂μ)
      atTop (𝓝 0))
    (hm : ∀ n, AEStronglyMeasurable (m n) μ) (hq : AEStronglyMeasurable q μ)
    (hC : 0 ≤ C) (hmBound : ∀ n, ∀ᵐ ω ∂μ, |m n ω| ≤ C)
    (hqBound : ∀ᵐ ω ∂μ, |q ω| ≤ C)
    (hmconv : ∀ᵐ ω ∂μ, Tendsto (fun n => m n ω) atTop (𝓝 (q ω))) :
    Tendsto (fun n => ∫ ω,
      |m n ω * (∑' i, (a n i ω) ^ 2) - q ω * (∑' i, (b i ω) ^ 2)| ∂μ)
      atTop (𝓝 0) := by
  apply tendsto_integral_abs_mul_sub
    (fun n => (DiscrepancyEnergy.sq_row_integrable_of_summable_integrals
      (fun i => (ha n i).integrable_sq) (haSum n)).2)
    (DiscrepancyEnergy.sq_row_integrable_of_summable_integrals
      (fun i => (hb i).integrable_sq) hbSum).2
    hm hq hC hmBound hqBound
  · exact tendsto_integral_abs_tsum_sq_sub ha hb haSum hbSum hlim
  · exact hmconv

theorem integral_abs_timePrimitive_le [SFinite μ]
    {E : ℝ → Ω → ℝ} {T t : ℝ} (ht : t ∈ Set.Icc 0 T)
    (hE : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Set.Ioc 0 T)).prod μ)) :
    (∫ ω, |∫ s in (0 : ℝ)..t, E s ω| ∂μ) ≤
      ∫ p : ℝ × Ω, |E p.1 p.2| ∂(volume.restrict (Set.Ioc 0 T)).prod μ := by
  have hmeasure : (volume.restrict (Set.Ioc 0 t)).prod μ ≤
      (volume.restrict (Set.Ioc 0 T)).prod μ :=
    Measure.prod_mono (Measure.restrict_mono_set _ (Set.Ioc_subset_Ioc_right ht.2)) le_rfl
  have hEt := hE.mono_measure hmeasure
  simp only [intervalIntegral.integral_of_le ht.1]
  calc
    _ ≤ ∫ ω, (∫ s in Set.Ioc 0 t, |E s ω|) ∂μ := by
      apply integral_mono hEt.integral_prod_right.abs hEt.abs.integral_prod_right
      intro ω
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun s => E s ω)
    _ = ∫ p : ℝ × Ω, |E p.1 p.2| ∂(volume.restrict (Set.Ioc 0 t)).prod μ :=
      (integral_prod_symm _ hEt.abs).symm
    _ ≤ _ := integral_mono_measure hmeasure
      (Eventually.of_forall (fun p => abs_nonneg (E p.1 p.2))) hE.abs

theorem integral_abs_timePrimitive_sub_le [SFinite μ]
    {E F : ℝ → Ω → ℝ} {T t : ℝ} (ht : t ∈ Set.Icc 0 T)
    (hE : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Set.Ioc 0 T)).prod μ))
    (hF : Integrable (fun p : ℝ × Ω => F p.1 p.2)
      ((volume.restrict (Set.Ioc 0 T)).prod μ)) :
    (∫ ω, |(∫ s in (0 : ℝ)..t, E s ω) - ∫ s in (0 : ℝ)..t, F s ω| ∂μ) ≤
      ∫ p : ℝ × Ω, |E p.1 p.2 - F p.1 p.2|
        ∂(volume.restrict (Set.Ioc 0 T)).prod μ := by
  have hmeasure : (volume.restrict (Set.Ioc 0 t)).prod μ ≤
      (volume.restrict (Set.Ioc 0 T)).prod μ :=
    Measure.prod_mono (Measure.restrict_mono_set _ (Set.Ioc_subset_Ioc_right ht.2)) le_rfl
  have hEt := hE.mono_measure hmeasure
  have hFt := hF.mono_measure hmeasure
  calc
    _ = ∫ ω, |∫ s in (0 : ℝ)..t, E s ω - F s ω| ∂μ := by
      apply integral_congr_ae
      filter_upwards [hEt.prod_left_ae, hFt.prod_left_ae] with ω hEω hFω
      simp only [intervalIntegral.integral_of_le ht.1]
      rw [integral_sub hEω hFω]
    _ ≤ _ := integral_abs_timePrimitive_le ht (hE.sub hF)

theorem timePrimitive_sub_tendsto_uniform_L1 [SFinite μ]
    {N : Type*} {l : Filter N} {E : N → ℝ → Ω → ℝ} {F : ℝ → Ω → ℝ} {T : ℝ}
    (hE : ∀ n, Integrable (fun p : ℝ × Ω => E n p.1 p.2)
      ((volume.restrict (Set.Ioc 0 T)).prod μ))
    (hF : Integrable (fun p : ℝ × Ω => F p.1 p.2)
      ((volume.restrict (Set.Ioc 0 T)).prod μ))
    (hlim : Tendsto (fun n => ∫ p : ℝ × Ω, |E n p.1 p.2 - F p.1 p.2|
      ∂(volume.restrict (Set.Ioc 0 T)).prod μ) l (𝓝 0)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in l, ∀ t ∈ Set.Icc 0 T,
      (∫ ω, |(∫ s in (0 : ℝ)..t, E n s ω) - ∫ s in (0 : ℝ)..t, F s ω| ∂μ) < ε := by
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  intro t ht
  exact (integral_abs_timePrimitive_sub_le ht (hE n) hF).trans_lt hn

theorem tendsto_integral_abs_mul_sub_of_tendstoInMeasure
    {E : ℕ → Ω → ℝ} {F : Ω → ℝ} {m : ℕ → Ω → ℝ} {q : Ω → ℝ} {C : ℝ}
    (hE : ∀ n, Integrable (E n) μ) (hF : Integrable F μ)
    (hm : ∀ n, AEStronglyMeasurable (m n) μ) (hq : AEStronglyMeasurable q μ)
    (hC : 0 ≤ C) (hmBound : ∀ n, ∀ᵐ ω ∂μ, |m n ω| ≤ C)
    (hqBound : ∀ᵐ ω ∂μ, |q ω| ≤ C)
    (hEconv : Tendsto (fun n => ∫ ω, |E n ω - F ω| ∂μ) atTop (𝓝 0))
    (hmconv : TendstoInMeasure μ m atTop q) :
    Tendsto (fun n => ∫ ω, |m n ω * E n ω - q ω * F ω| ∂μ) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, hmae⟩ := (hmconv.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  exact tendsto_integral_abs_mul_sub
    (fun n => hE (ns (ms n))) hF (fun n => hm (ns (ms n))) hq hC
    (fun n => hmBound (ns (ms n))) hqBound
    (hEconv.comp (hns.comp hms.tendsto_atTop)) hmae

theorem tendstoInMeasure_of_integral_sq_sub
    {m : ℕ → Ω → ℝ} {q : Ω → ℝ}
    (hm : ∀ n, MemLp (m n) 2 μ) (hq : MemLp q 2 μ)
    (hlim : Tendsto (fun n => ∫ ω, (m n ω - q ω) ^ 2 ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ m atTop q := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
  have heq n : eLpNorm (m n - q) 2 μ =
      ENNReal.ofReal (Real.sqrt (∫ ω, (m n ω - q ω) ^ 2 ∂μ)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      ((hm n).sub hq)]
    simp only [ENNReal.toReal_ofNat, Pi.sub_apply, Real.rpow_two, Real.norm_eq_abs,
      sq_abs, Real.sqrt_eq_rpow, one_div]
  simp only [heq]
  simpa only [Function.comp_def, Real.sqrt_zero, ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim.sqrt

theorem tendsto_integral_abs_mul_sub_of_meanSquare
    {E : ℕ → Ω → ℝ} {F : Ω → ℝ} {m : ℕ → Ω → ℝ} {q : Ω → ℝ} {C : ℝ}
    (hE : ∀ n, Integrable (E n) μ) (hF : Integrable F μ)
    (hm : ∀ n, MemLp (m n) 2 μ) (hq : MemLp q 2 μ)
    (hC : 0 ≤ C) (hmBound : ∀ n, ∀ᵐ ω ∂μ, |m n ω| ≤ C)
    (hqBound : ∀ᵐ ω ∂μ, |q ω| ≤ C)
    (hEconv : Tendsto (fun n => ∫ ω, |E n ω - F ω| ∂μ) atTop (𝓝 0))
    (hmconv : Tendsto (fun n => ∫ ω, (m n ω - q ω) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |m n ω * E n ω - q ω * F ω| ∂μ) atTop (𝓝 0) :=
  tendsto_integral_abs_mul_sub_of_tendstoInMeasure hE hF
    (fun n => (hm n).aestronglyMeasurable) hq.aestronglyMeasurable
    hC hmBound hqBound hEconv (tendstoInMeasure_of_integral_sq_sub hm hq hmconv)

end Problem367.RowEnergyL1

end

end OAI
