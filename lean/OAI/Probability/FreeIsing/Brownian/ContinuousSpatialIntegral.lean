import OAI.Probability.FreeIsing.Brownian.ArrayFiltrationIntegral
import OAI.Probability.FreeIsing.Brownian.IntegralHorizon
import OAI.Probability.FreeIsing.Martingales.SpatialLimit

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ι → ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem stopped_grid_sums_orthogonal [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ι → ℕ → Ω → ℝ)
    (hH : ∀ a i, StronglyMeasurable[F (τ i)] (H a i))
    (hH2 : ∀ a i, MemLp (H a i) 2 P)
    {a b : ι} (hab : a ≠ b) (u v : Finset ℕ) (t : ℝ≥0) :
    (∫ ω,
      (∑ i ∈ u, StoppedSimpleIntegral.intervalSum (B a) (H a i) (τ i) (τ (i + 1)) t ω) *
      (∑ i ∈ v, StoppedSimpleIntegral.intervalSum (B b) (H b i) (τ i) (τ (i + 1)) t ω)
      ∂P) = 0 := by
  classical
  let σ : ℕ → ℝ≥0 := fun i => min t (τ i)
  let G : ι → ℕ → Ω → ℝ := fun a i => if τ i ≤ t then H a i else 0
  have hσ : Monotone σ := fun i j hij => min_le_min_left t (hτ hij)
  have hG (a : ι) (i : ℕ) : StronglyMeasurable[F (σ i)] (G a i) := by
    change StronglyMeasurable[F (min t (τ i))] (if τ i ≤ t then H a i else 0)
    by_cases hi : τ i ≤ t
    · rw [ite_eq_left hi, min_eq_right hi]
      exact hH a i
    · rw [ite_eq_right hi]
      exact stronglyMeasurable_zero
  have hG2 (a : ι) (i : ℕ) : MemLp (G a i) 2 P := by
    by_cases hi : τ i ≤ t
    · simpa only [G, ite_eq_left hi] using hH2 a i
    · simp only [G, ite_eq_right hi]
      exact MemLp.zero
  have hterm (a : ι) (i : ℕ) (ω : Ω) :
      StoppedSimpleIntegral.intervalSum (B a) (H a i) (τ i) (τ (i + 1)) t ω =
        G a i ω * (B a (σ (i + 1)) ω - B a (σ i) ω) := by
    by_cases hi : τ i ≤ t
    · simp only [G, ite_eq_left hi, σ, StoppedSimpleIntegral.intervalSum]
    · have hti : t ≤ τ i := le_of_not_ge hi
      have hti' : t ≤ τ (i + 1) := hti.trans (hτ (Nat.le_succ i))
      simp only [G, ite_eq_right hi, σ, StoppedSimpleIntegral.intervalSum,
        min_eq_left hti, min_eq_left hti', sub_self, mul_zero, Pi.zero_apply]
  simp_rw [hterm]
  exact grid_sums_orthogonal hB hAd hind hcross σ hσ G hG hG2 hab u v

theorem stopped_uniform_limits_orthogonal [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    {H : ι → ℝ≥0 → Ω → ℝ} (hH : ∀ a, StronglyAdapted F (H a))
    (hH2 : ∀ a t, MemLp (H a t) 2 P) (T t : ℝ≥0)
    {I : ι → Ω → ℝ} (hI2 : ∀ a, MemLp (I a) 2 P)
    (hlim : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) T n t ω - I a ω) ^ 2 ∂P)
      atTop (𝓝 0)) :
    Pairwise (fun a b => ∫ ω, I a ω * I b ω ∂P = 0) := by
  have hi (a : ι) (s t : ℝ≥0) (hst : s ≤ t) :
      Indep (MeasurableSpace.comap (fun ω => B a t ω - B a s ω) inferInstance) (F s) P :=
    coordinate_increment_indep_past (hind s t hst) a
  have hS2 (a : ι) (n : ℕ) :
      MemLp (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) T n t) 2 P :=
    BrownianFiltration.stopped_predictable_sum_memLp_two (hB a) (hi a)
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun i => H a (BrownianGrid.uniformGrid T n i)) (fun i => hH a _) (fun i => hH2 a _)
      (Finset.range n) t
  have hLp (a : ι) := BrownianIntegralProcess.L2_tendsto_of_integral_sq_sub_tendsto
    (hS2 a) (hI2 a) (hlim a)
  intro a b hab
  have hinner := (hLp a).inner (𝕜 := ℝ) (hLp b)
  have hz (n : ℕ) : inner ℝ
      ((hS2 a n).toLp (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) T n t))
      ((hS2 b n).toLp (BrownianIntegralProcess.stoppedUniformSum (B b) (H b) T n t)) = 0 := by
    rw [PredictableL2.inner_toLp]
    exact stopped_grid_sums_orthogonal hB hAd hind hcross
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun a i => H a (BrownianGrid.uniformGrid T n i))
      (fun a i => hH a _) (fun a i => hH2 a _) hab (Finset.range n) (Finset.range n) t
  have heq : inner ℝ ((hI2 a).toLp (I a)) ((hI2 b).toLp (I b)) = 0 :=
    tendsto_nhds_unique hinner (by simpa only [hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  simpa only [PredictableL2.inner_toLp] using heq

theorem exists_global_continuous_spatial_integral [Countable ι] [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (H : ι → ℝ≥0 → Ω → ℝ) (hH : ∀ a, StronglyAdapted F (H a))
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (C : ι → ℝ) (hC : ∀ a, 0 ≤ C a)
    (hb : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
    (henergy : ∀ N : ℕ, Summable (fun a =>
      ∫ s in (0 : ℝ)..(N : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P)) :
    ∃ (I : ι → ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ)
      (hI2 : ∀ a t, MemLp (I a t) 2 P) (hY2 : ∀ t, MemLp (Y t) 2 P),
      (∀ a, IsStronglyPredictable F (I a) ∧ Martingale (I a) F P ∧
        (∀ᵐ ω ∂P, Continuous (fun t => I a t ω))) ∧
      (∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
        Tendsto (fun n => ∫ ω,
          (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω - I a t ω) ^ 2 ∂P)
          atTop (𝓝 0)) ∧
      IsStronglyPredictable F Y ∧ Martingale Y F P ∧
      (∀ᵐ ω ∂P, Continuous (fun t => Y t ω)) ∧ Y 0 =ᵐ[P] 0 ∧
      (∀ t, (∫ ω, Y t ω ∂P) = 0) ∧
      (∀ t, (∫ ω, Y t ω ^ 2 ∂P) =
        ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P) ∧
      (∀ t, HasSum (fun a => (hI2 a t).toLp (I a t)) ((hY2 t).toLp (Y t))) ∧
      (∀ T : ℝ≥0, Tendsto (fun q : Finset ι =>
        ∫ ω, MartingaleStrongMaximal.maximalSquare
          (MartingaleSpatialLimit.finiteSum I q - Y) T ω ∂P) atTop (𝓝 0)) := by
  have hi (a : ι) (s t : ℝ≥0) (hst : s ≤ t) :
      Indep (MeasurableSpace.comap (fun ω => B a t ω - B a s ω) inferInstance) (F s) P :=
    coordinate_increment_indep_past (hind s t hst) a
  have hH2 (a : ι) (t : ℝ≥0) : MemLp (H a t) 2 P := by
    apply MemLp.of_bound ((hH a t).mono (F.le t)).aestronglyMeasurable (C a)
    filter_upwards [hb a] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hex (a : ι) := BrownianIntegralProcess.exists_global_continuous_uniform_integral
    (hB a) (hAd a) (hi a) (hBc a) (hH a) (hc a) (hC a) (hb a)
  choose I hIp hIM hIc hI2 hIz hImean hIiso hIlim using hex
  have horth (t : ℝ≥0) : Pairwise (fun a b => ∫ ω, I a t ω * I b t ω ∂P = 0) := by
    obtain ⟨N, hN⟩ := exists_nat_ge t
    have ht : t ≤ ((N + 1 : ℕ) : ℝ≥0) :=
      hN.trans (by exact_mod_cast Nat.le_succ N)
    exact stopped_uniform_limits_orthogonal hB hAd hind hcross hH hH2
      ((N + 1 : ℕ) : ℝ≥0) t (fun a => hI2 a t)
      (fun a => hIlim a (N + 1) (Nat.succ_pos N) t ht)
  have hIenergy (N : ℕ) : Summable (fun a => ∫ ω, I a (N : ℝ≥0) ω ^ 2 ∂P) := by
    simpa only [hIiso, NNReal.coe_natCast] using henergy N
  obtain ⟨Y, hY2, hYp, hYM, hYc, hYsum, hYmax⟩ :=
    MartingaleSpatialLimit.exists_continuous_martingale_sum hIM hI2 hIc horth hIenergy
  have hYiso (t : ℝ≥0) : (∫ ω, Y t ω ^ 2 ∂P) =
      ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P := by
    have he := MartingaleSpatialLimit.summable_energy_of_integer hIM hI2 hIenergy t
    have hinner : Pairwise (fun a b => inner ℝ
        ((hI2 a t).toLp (I a t)) ((hI2 b t).toLp (I b t)) = 0) := by
      intro a b hab
      simpa only [PredictableL2.inner_toLp] using horth t hab
    have hn := PredictableL2.norm_tsum_sq_of_orthogonal
      (fun a => (hI2 a t).toLp (I a t)) hinner
      (by simpa only [PredictableL2.norm_toLp_sq] using he)
    rw [(hYsum t).tsum_eq] at hn
    simpa only [PredictableL2.norm_toLp_sq, hIiso] using hn
  have hYzero : Y 0 =ᵐ[P] 0 := by
    apply ae_eq_of_integral_sq_sub_eq_zero
    · simpa only [Pi.zero_apply, sub_zero] using (hY2 0).integrable_sq
    · simpa only [Pi.zero_apply, sub_zero, NNReal.coe_zero,
        intervalIntegral.integral_same, tsum_zero] using hYiso 0
  exact ⟨I, Y, hI2, hY2, (fun a => ⟨hIp a, hIM a, hIc a⟩), hIlim,
    hYp, hYM, hYc, hYzero,
    (fun t => PredictableL2.integral_eq_zero_of_hasSum
      (fun a => I a t) (fun a => hI2 a t) (hY2 t) (hYsum t) (fun a => hImean a t)),
    hYiso, hYsum, hYmax⟩

end Problem367.BrownianArrayFiltration

end

end OAI
