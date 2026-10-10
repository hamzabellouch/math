import OAI.Probability.FreeIsing.Brownian.ContinuousSpatialIntegral
import OAI.Probability.FreeIsing.Brownian.RowEnergyCompletion

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.MartingaleSquareMaximal

theorem exists_global_continuous_meanSquare_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {M : ℕ → ℝ≥0 → Ω → ℝ}
    (hM : ∀ n, Martingale (M n) F P)
    (h2 : ∀ n t, MemLp (M n t) 2 P)
    (hc : ∀ n, ∀ᵐ ω ∂P, Continuous (fun t => M n t ω))
    (hC : ∀ N : ℕ, 0 < N → ∀ ε > (0 : ℝ), ∃ k : ℕ,
      ∀ n ≥ k, ∀ m ≥ k, (∫ ω, (M n N ω - M m N ω) ^ 2 ∂P) < ε) :
    ∃ (Z : ℝ≥0 → Ω → ℝ) (_hZ2 : ∀ t, MemLp (Z t) 2 P),
      IsStronglyPredictable F Z ∧ Martingale Z F P ∧
      (∀ᵐ ω ∂P, Continuous (fun t => Z t ω)) ∧
      (∀ t, Tendsto (fun n => ∫ ω, (M n t ω - Z t ω) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ t, Tendsto (fun n => ∫ ω, M n t ω ^ 2 ∂P) atTop
        (𝓝 (∫ ω, Z t ω ^ 2 ∂P))) ∧
      (∀ T, Tendsto (fun n => ∫ ω,
        MartingaleStrongMaximal.maximalSquare (M n - Z) T ω ∂P) atTop (𝓝 0)) := by
  have hCpos (N : ℕ) (hN : 0 < N) :
      CauchySeq (fun n => (h2 n (N : ℝ≥0)).toLp (M n N)) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := hC N hN (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨k, fun n hn m hm => ?_⟩
    have hs := hk n hn m hm
    rw [← dist_toLp_sq (h2 n N) (h2 m N)] at hs
    nlinarith [dist_nonneg (x := (h2 n N).toLp (M n N))
      (y := (h2 m N).toLp (M m N))]
  have hCall (N : ℕ) : CauchySeq (fun n => (h2 n (N : ℝ≥0)).toLp (M n N)) :=
    L2_cauchy_of_le hM h2 (by exact_mod_cast Nat.le_succ N)
      (hCpos (N + 1) (Nat.succ_pos N))
  obtain ⟨Z, hpZ, hcZ, hlZ⟩ :=
    exists_global_predictable_continuous_L2_limit hM h2 hc hCall
  choose hZ2 hl using hlZ
  have hmartZ : Martingale Z F P :=
    martingale_of_L2_limits hM h2 hpZ.stronglyAdapted hZ2 hl
  have hmean (t : ℝ≥0) := BrownianIntegralProcess.integral_sq_sub_tendsto_of_L2_tendsto
    (fun n => h2 n t) (hZ2 t) (hl t)
  refine ⟨Z, hZ2, hpZ, hmartZ, hcZ, hmean, ?_, ?_⟩
  · intro t
    simpa only [PredictableL2.norm_toLp_sq] using (hl t).norm.pow 2
  · intro T
    apply squeeze_zero (fun n => integral_nonneg (fun ω => ENNReal.toReal_nonneg))
      (fun n => ?_) (show Tendsto
        (fun n => 4 * ∫ ω, (M n T ω - Z T ω) ^ 2 ∂P) atTop (𝓝 0) from by
          simpa only [mul_zero] using (hmean T).const_mul 4)
    exact MartingaleStrongMaximal.integral_maximalSquare_le
      ((hM n).sub hmartZ) (fun t => (h2 n t).sub (hZ2 t))
      (by filter_upwards [hc n, hcZ] with ω hn hz; exact hn.sub hz) T

end Problem367.MartingaleSquareMaximal

namespace Problem367.BrownianArrayFiltration

theorem exists_global_continuous_integral_limit_of_row_energy_cauchy
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ι → ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (H : ℕ → ι → ℝ≥0 → Ω → ℝ)
    (hH : ∀ n a, StronglyAdapted F (H n a))
    (hcH : ∀ n a, ∀ᵐ ω ∂P, Continuous (fun t => H n a t ω))
    (C : ℕ → ι → ℝ) (hC : ∀ n a, 0 ≤ C n a)
    (hbH : ∀ n a, ∀ᵐ ω ∂P, ∀ t, |H n a t ω| ≤ C n a)
    (he : ∀ n (N : ℕ), Summable fun a => ∫ t in (0 : ℝ)..(N : ℝ),
      ∫ ω, H n a t.toNNReal ω ^ 2 ∂P)
    (hCauchy : ∀ N : ℕ, 0 < N → ∀ ε > (0 : ℝ), ∃ k : ℕ,
      ∀ n ≥ k, ∀ m ≥ k, (∑' a, ∫ t in (0 : ℝ)..(N : ℝ),
        ∫ ω, (H n a t.toNNReal ω - H m a t.toNNReal ω) ^ 2 ∂P) < ε) :
    ∃ (I : ℕ → ι → ℝ≥0 → Ω → ℝ) (Y : ℕ → ℝ≥0 → Ω → ℝ)
      (Z : ℝ≥0 → Ω → ℝ)
      (hI2 : ∀ n a t, MemLp (I n a t) 2 P)
      (hY2 : ∀ n t, MemLp (Y n t) 2 P) (_hZ2 : ∀ t, MemLp (Z t) 2 P),
      (∀ n, IsStronglyPredictable F (Y n) ∧ Martingale (Y n) F P ∧
        (∀ᵐ ω ∂P, Continuous (fun t => Y n t ω))) ∧
      (∀ n a (N : ℕ), 0 < N → Tendsto (fun k => ∫ ω,
        (BrownianGrid.uniformSum (B a) (H n a) N k ω - I n a N ω) ^ 2 ∂P)
          atTop (𝓝 0)) ∧
      (∀ n t, HasSum (fun a => (hI2 n a t).toLp (I n a t))
        ((hY2 n t).toLp (Y n t))) ∧
      (∀ n t, (∫ ω, Y n t ω ^ 2 ∂P) =
        ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, H n a s.toNNReal ω ^ 2 ∂P) ∧
      (∀ n m (N : ℕ), 0 < N → (∫ ω, (Y n N ω - Y m N ω) ^ 2 ∂P) =
        ∑' a, ∫ s in (0 : ℝ)..(N : ℝ),
          ∫ ω, (H n a s.toNNReal ω - H m a s.toNNReal ω) ^ 2 ∂P) ∧
      IsStronglyPredictable F Z ∧ Martingale Z F P ∧
      (∀ᵐ ω ∂P, Continuous (fun t => Z t ω)) ∧ Z 0 =ᵐ[P] 0 ∧
      (∀ t, (∫ ω, Z t ω ∂P) = 0) ∧
      (∀ t, Tendsto (fun n => ∫ ω, (Y n t ω - Z t ω) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ t : ℝ≥0, Tendsto (fun n => ∑' a, ∫ s in (0 : ℝ)..(t : ℝ),
        ∫ ω, H n a s.toNNReal ω ^ 2 ∂P) atTop (𝓝 (∫ ω, Z t ω ^ 2 ∂P))) ∧
      (∀ T, Tendsto (fun n => ∫ ω,
        MartingaleStrongMaximal.maximalSquare (Y n - Z) T ω ∂P) atTop (𝓝 0)) := by
  have hex (n : ℕ) := exists_global_continuous_spatial_integral
    hB hAd hind hcross hBc (H n) (hH n) (hcH n) (C n) (hC n) (hbH n) (he n)
  choose I Y hI2 hY2 hIprop haI hpY hmY hcY hzY hmeanY heY hsY hmaxY using hex
  have ha (n : ℕ) (a : ι) (N : ℕ) (hN : 0 < N) :
      Tendsto (fun k => ∫ ω,
        (BrownianGrid.uniformSum (B a) (H n a) N k ω - I n a N ω) ^ 2 ∂P)
          atTop (𝓝 0) := by
    simpa only [BrownianIntegralProcess.stoppedUniformSum_terminal] using
      haI n a N hN N le_rfl
  have hs (n : ℕ) (t : ℝ≥0) : Tendsto (fun s : Finset ι => ∫ ω,
      ((∑ a ∈ s, I n a t ω) - Y n t ω) ^ 2 ∂P) atTop (𝓝 0) :=
    PredictableL2.tendsto_integral_sq_error_of_hasSum
      (fun a => I n a t) (fun a => hI2 n a t) (hY2 n t) (hsY n t)
  have hpair (n m N : ℕ) (hN : 0 < N) :
      (∫ ω, (Y n N ω - Y m N ω) ^ 2 ∂P) =
        ∑' a, ∫ s in (0 : ℝ)..(N : ℝ),
          ∫ ω, (H n a s.toNNReal ω - H m a s.toNNReal ω) ^ 2 ∂P :=
    infinite_row_difference_isometry_of_row_energies hB hAd hind
      (H n) (H m) (hH n) (hH m) (hcH n) (hcH m)
      (C n) (C m) (hC n) (hC m) (hbH n) (hbH m) N (he n N) (he m N)
      hcross (fun a => hI2 n a N) (fun a => hI2 m a N)
      (fun a => ha n a N hN) (fun a => ha m a N hN)
      (hY2 n N) (hY2 m N) (hs n N) (hs m N)
  have hCY (N : ℕ) (hN : 0 < N) : ∀ ε > (0 : ℝ), ∃ k : ℕ,
      ∀ n ≥ k, ∀ m ≥ k, (∫ ω, (Y n N ω - Y m N ω) ^ 2 ∂P) < ε := by
    simpa only [hpair _ _ N hN] using hCauchy N hN
  obtain ⟨Z, hZ2, hpZ, hmZ, hcZ, hlZ, heZ, hmaxZ⟩ :=
    MartingaleSquareMaximal.exists_global_continuous_meanSquare_limit hmY hY2 hcY hCY
  have hzZ : Z 0 =ᵐ[P] 0 := by
    have hzero (n : ℕ) : (∫ ω, Y n 0 ω ^ 2 ∂P) = 0 := by
      simp only [heY, NNReal.coe_zero, intervalIntegral.integral_same, tsum_zero]
    have henergy0 : (∫ ω, Z 0 ω ^ 2 ∂P) = 0 :=
      tendsto_nhds_unique (heZ 0) (by simpa only [hzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    apply ae_eq_of_integral_sq_sub_eq_zero
    · simpa only [Pi.zero_apply, sub_zero] using (hZ2 0).integrable_sq
    · simpa only [Pi.zero_apply, sub_zero] using henergy0
  have hcenter (t : ℝ≥0) : (∫ ω, Z t ω ∂P) = 0 := by
    have hlim := BrownianIntegralProcess.L2_tendsto_of_integral_sq_sub_tendsto
      (fun n => hY2 n t) (hZ2 t) (hlZ t)
    have hi := (tendsto_const_nhds (x := (memLp_const (1 : ℝ)).toLp
      (fun _ : Ω => (1 : ℝ)))).inner (𝕜 := ℝ) hlim
    simp only [PredictableL2.inner_toLp, one_mul, hmeanY] at hi
    exact tendsto_nhds_unique hi tendsto_const_nhds
  refine ⟨I, Y, Z, hI2, hY2, hZ2, (fun n => ⟨hpY n, hmY n, hcY n⟩), ha,
    hsY, heY, hpair, hpZ, hmZ, hcZ, hzZ, hcenter, hlZ, ?_, hmaxZ⟩
  intro t
  simpa only [heY] using heZ t

end Problem367.BrownianArrayFiltration

end

end OAI
