import OAI.Probability.FreeIsing.Brownian.FiltrationUniformIntegral

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianFiltrationGrid
open BrownianGrid

theorem uniformSum_stronglyMeasurable_terminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (_hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted (F) H)
    (T : ℝ≥0) (n : ℕ) :
    StronglyMeasurable[F T] (uniformSum B H T n) := by
  by_cases hn : n = 0
  · subst n
    have hz : uniformSum B H T 0 = fun _ : Ω => (0 : ℝ) := by
      funext ω
      simp [uniformSum, integralSum]
    rw [hz]
    exact stronglyMeasurable_const
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  unfold uniformSum integralSum
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  have hi0 : i ≤ n := (Finset.mem_range.mp hi).le
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  have hti := uniformGrid_le_horizon T hn0 hi0
  have hti1 := uniformGrid_le_horizon T hn0 hi1
  exact ((hH _).mono ((F).mono hti)).mul
    (((hAd _).mono ((F).mono hti1)).sub
      ((hAd _).mono ((F).mono hti)))

theorem integral_integralSum_eq_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i))
    (hH2 : ∀ i, MemLp (H i) 2 P) (n : ℕ) :
    (∫ ω, integralSum B t H n ω ∂P) = 0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hD2 (i : ℕ) : MemLp (fun ω => B (t (i + 1)) ω - B (t i) ω) 2 P :=
    (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two.sub
      (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
  have hint (i : ℕ) : Integrable (fun ω => H i ω * (B (t (i + 1)) ω - B (t i) ω)) P :=
    (hH2 i).integrable_mul (hD2 i)
  unfold integralSum
  rw [integral_finsetSum _ (fun i _ => hint i)]
  apply Finset.sum_eq_zero
  intro i hi
  exact SimpleIntegral.integral_mul_eq_zero_of_condExp_eq_zero
    ((F).le _) (hH i) ((hD2 i).integrable (by norm_num)) (hint i)
    (BrownianFiltration.increment_condExp_zero hB hAd (hind _ _ (ht (Nat.le_succ i))))

theorem integral_sq_error_tendsto_of_Lp_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0) {I : Lp ℝ 2 P}
    (hI : Tendsto (uniformSumLp hB hAd hind H hH hH2 T) atTop (𝓝 I)) :
    Tendsto (fun n => ∫ ω, (uniformSum B H T n ω - I ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hnorm := (hI.sub (tendsto_const_nhds (x := I))).norm.pow 2
  simp only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hnorm
  apply hnorm.congr'
  apply Filter.Eventually.of_forall
  intro n
  dsimp only
  rw [norm_sq_L2_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (uniformSumLp hB hAd hind H hH hH2 T n) I,
    coe_uniformSumLp hB hAd hind H hH hH2 T n] with ω hsub hsum
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hsum]

theorem uniformSumLp_limit_terminal_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0) {I : Lp ℝ 2 P}
    (hI : Tendsto (uniformSumLp hB hAd hind H hH hH2 T) atTop (𝓝 I)) :
    AEStronglyMeasurable[F T] (I : Ω → ℝ) P ∧
      (∫ ω, I ω ∂P) = 0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  constructor
  · apply (isClosed_aestronglyMeasurable ((F).le T)).mem_of_tendsto hI
    apply Filter.Eventually.of_forall
    intro n
    exact (uniformSum_stronglyMeasurable_terminal hAd hind H hH T n).aestronglyMeasurable.congr
      (coe_uniformSumLp hB hAd hind H hH hH2 T n).symm
  · have hinner := ((innerSL ℝ (Lp.const 2 P (1 : ℝ))).continuous.tendsto I).comp hI
    have hzero (n : ℕ) : inner ℝ (Lp.const 2 P (1 : ℝ)) (uniformSumLp hB hAd hind H hH hH2 T n) = 0 := by
      rw [inner_const_one_eq_integral]
      rw [integral_congr_ae (coe_uniformSumLp hB hAd hind H hH hH2 T n)]
      exact integral_integralSum_eq_zero hB hAd hind (uniformGrid T n) (uniformGrid_mono T n)
        (fun i => H (uniformGrid T n i)) (fun i => hH _) (fun i => hH2 _) n
    change Tendsto (fun n => inner ℝ (Lp.const 2 P (1 : ℝ))
      (uniformSumLp hB hAd hind H hH hH2 T n)) atTop
      (𝓝 (inner ℝ (Lp.const 2 P (1 : ℝ)) I)) at hinner
    have heq : inner ℝ (Lp.const 2 P (1 : ℝ)) I = 0 := by
      apply tendsto_nhds_unique hinner
      simpa only [hzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    simpa only [inner_const_one_eq_integral] using heq

theorem exists_terminal_uniform_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0)
    (hcont : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T → (t : ℝ) - (s : ℝ) ≤ δ →
        (∫ ω, (H s ω - H t ω) ^ 2 ∂P) ≤ ε) :
    ∃ I : Ω → ℝ, StronglyMeasurable[F T] I ∧ MemLp I 2 P ∧
      (∫ ω, I ω ∂P) = 0 ∧
      Tendsto (fun n => ∫ ω, (uniformSum B H T n ω - I ω) ^ 2 ∂P) atTop (𝓝 0) := by
  obtain ⟨I, hI⟩ := exists_uniformSumLp_limit hB hAd hind H hH hH2 T hcont
  obtain ⟨hIm, hIzero⟩ := uniformSumLp_limit_terminal_centered hB hAd hind H hH hH2 T hI
  refine ⟨hIm.mk I, hIm.stronglyMeasurable_mk, ?_, ?_, ?_⟩
  · exact MemLp.ae_eq hIm.ae_eq_mk (Lp.memLp I)
  · exact (integral_congr_ae hIm.ae_eq_mk).symm.trans hIzero
  · apply (integral_sq_error_tendsto_of_Lp_tendsto hB hAd hind H hH hH2 T hI).congr'
    apply Filter.Eventually.of_forall
    intro n
    apply integral_congr_ae
    filter_upwards [hIm.ae_eq_mk] with ω hω
    rw [hω]

theorem exists_terminal_uniform_integral_of_bounded_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T : ℝ≥0) :
    ∃ I : Ω → ℝ, StronglyMeasurable[F T] I ∧ MemLp I 2 P ∧
      (∫ ω, I ω ∂P) = 0 ∧
      Tendsto (fun n => ∫ ω, (uniformSum B H T n ω - I ω) ^ 2 ∂P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hHm : ∀ t, AEStronglyMeasurable (H t) P := fun t =>
    ((hH t).mono ((F).le t)).aestronglyMeasurable
  have hH2 : ∀ t, MemLp (H t) 2 P := by
    intro t
    apply MemLp.of_bound (hHm t) C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  apply exists_terminal_uniform_integral hB hAd hind H hH hH2 T
  intro ε hε
  exact MeanSquareContinuity.uniform_integral_sq_sub_le hHm hc hC hb T hε

theorem exists_terminal_uniform_integral_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T : ℝ≥0) :
    ∃ I : Ω → ℝ, StronglyMeasurable[F T] I ∧ MemLp I 2 P ∧
      (∫ ω, I ω ∂P) = 0 ∧
      (∫ ω, (I ω) ^ 2 ∂P) = (∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, (H t.toNNReal ω) ^ 2 ∂P) ∧
      Tendsto (fun n => ∫ ω, (uniformSum B H T n ω - I ω) ^ 2 ∂P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hHm : ∀ t, AEStronglyMeasurable (H t) P := fun t =>
    ((hH t).mono ((F).le t)).aestronglyMeasurable
  have hH2 : ∀ t, MemLp (H t) 2 P := by
    intro t
    apply MemLp.of_bound (hHm t) C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  obtain ⟨I, hI⟩ := exists_uniformSumLp_limit hB hAd hind H hH hH2 T
    (fun _ hε => MeanSquareContinuity.uniform_integral_sq_sub_le hHm hc hC hb T hε)
  obtain ⟨hIm, hIzero⟩ := uniformSumLp_limit_terminal_centered hB hAd hind H hH hH2 T hI
  have hiso := uniformSumLp_limit_isometry hB hAd hind H hH hH2 hc hC hb T hI
  refine ⟨hIm.mk I, hIm.stronglyMeasurable_mk, MemLp.ae_eq hIm.ae_eq_mk (Lp.memLp I), ?_, ?_, ?_⟩
  · exact (integral_congr_ae hIm.ae_eq_mk).symm.trans hIzero
  · rw [← hiso]
    apply integral_congr_ae
    filter_upwards [hIm.ae_eq_mk] with ω hω
    rw [hω]
  · apply (integral_sq_error_tendsto_of_Lp_tendsto hB hAd hind H hH hH2 T hI).congr'
    apply Filter.Eventually.of_forall
    intro n
    apply integral_congr_ae
    filter_upwards [hIm.ae_eq_mk] with ω hω
    rw [hω]

end Problem367.BrownianFiltrationGrid

end

end OAI
