import OAI.Probability.FreeIsing.Brownian.ContinuousCross
import OAI.Probability.FreeIsing.Brownian.ContinuousSpatialIntegral
import OAI.Probability.FreeIsing.Brownian.GlobalCompensator
import OAI.Probability.FreeIsing.Martingales.SpatialCompensator

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ}

def nonnegativeCompensator (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  max (BrownianIntegralProcess.globalCompensator H t ω) 0

def spatialCompensator (H : ι → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑' a, nonnegativeCompensator (H a) t ω

theorem nonnegativeCompensator_stronglyAdapted
    {H : ℝ≥0 → Ω → ℝ} (hH : StronglyAdapted F H) :
    StronglyAdapted F (nonnegativeCompensator H) := by
  intro t
  have hm := BrownianIntegralProcess.globalCompensator_stronglyAdapted hH t
  let : MeasurableSpace Ω := F t
  exact hm.sup stronglyMeasurable_const

theorem ae_nonnegativeCompensator_eq_global
    {H : ℝ≥0 → Ω → ℝ} (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) :
    ∀ᵐ ω ∂P, ∀ t, nonnegativeCompensator H t ω =
      BrownianIntegralProcess.globalCompensator H t ω := by
  filter_upwards [BrownianIntegralProcess.ae_globalCompensator_eq_integral hc] with ω hω
  intro t
  unfold nonnegativeCompensator
  apply max_eq_left
  rw [hω t]
  exact intervalIntegral.integral_nonneg t.coe_nonneg (fun s _ => sq_nonneg _)

omit mΩ in
@[simp] theorem nonnegativeCompensator_zero (H : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    nonnegativeCompensator H 0 ω = 0 := by
  simp [nonnegativeCompensator, BrownianIntegralProcess.globalCompensator]

theorem nonnegativeCompensator_integrable [IsFiniteMeasure P]
    {H : ℝ≥0 → Ω → ℝ} (hH : StronglyAdapted F H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C) (t : ℝ≥0) :
    Integrable (nonnegativeCompensator H t) P := by
  have hi : Integrable (BrownianIntegralProcess.globalCompensator H t) P :=
    (SelectedCompensator.selected_memLp hH hc hC hb t t 1).integrable le_rfl
  exact hi.sup (integrable_const 0)

theorem spatialCompensator_stronglyAdapted [Countable ι]
    {H : ι → ℝ≥0 → Ω → ℝ} (hH : ∀ a, StronglyAdapted F (H a)) :
    StronglyAdapted F (spatialCompensator H) := by
  intro t
  have hm (a : ι) := nonnegativeCompensator_stronglyAdapted (hH a) t
  let : MeasurableSpace Ω := F t
  exact StronglyMeasurable.tsum hm

theorem ae_spatialCompensator_eq_integral_sum [Countable ι]
    {H : ι → ℝ≥0 → Ω → ℝ}
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω)) :
    ∀ᵐ ω ∂P, ∀ t, spatialCompensator H t ω =
      ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), (H a s.toNNReal ω) ^ 2 := by
  have heq := ae_all_iff.mpr (fun a => ae_nonnegativeCompensator_eq_global (hc a))
  have hint := ae_all_iff.mpr (fun a =>
    BrownianIntegralProcess.ae_globalCompensator_eq_integral (hc a))
  filter_upwards [heq, hint] with ω hω hω'
  intro t
  exact tsum_congr (fun a => (hω a t).trans (hω' a t))

theorem integral_nonnegativeCompensator_eq_sq [IsFiniteMeasure P]
    {H I : ℝ≥0 → Ω → ℝ}
    (hQ : Martingale (fun t ω => I t ω ^ 2 - nonnegativeCompensator H t ω) F P)
    (hI2 : ∀ t, MemLp (I t) 2 P) (hz : I 0 =ᵐ[P] 0)
    (hAint : ∀ t, Integrable (nonnegativeCompensator H t) P) (t : ℝ≥0) :
    (∫ ω, nonnegativeCompensator H t ω ∂P) = ∫ ω, I t ω ^ 2 ∂P := by
  have hzero : (∫ ω, I 0 ω ^ 2 - nonnegativeCompensator H 0 ω ∂P) = 0 := by
    calc
      _ = ∫ _ : Ω, (0 : ℝ) ∂P := by
        apply integral_congr_ae
        filter_upwards [hz] with ω hω
        simp only [hω, Pi.zero_apply, zero_pow (by norm_num : 2 ≠ 0),
          nonnegativeCompensator_zero, sub_zero]
      _ = 0 := integral_zero _ _
  have heq := hQ.setIntegral_eq (show (0 : ℝ≥0) ≤ t from bot_le) MeasurableSet.univ
  simp only [Measure.restrict_univ] at heq
  rw [hzero, integral_sub (hI2 t).integrable_sq (hAint t)] at heq
  linarith

theorem exists_global_continuous_spatial_integral_compensatedSquare
    [Countable ι] [IsProbabilityMeasure P]
    {B H : ι → ℝ≥0 → Ω → ℝ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (hH : ∀ a, StronglyAdapted F (H a))
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    {C : ι → ℝ} (hC : ∀ a, 0 ≤ C a)
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
      (∀ t, (∫ ω, Y t ω ^ 2 ∂P) =
        ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P) ∧
      (∀ t, HasSum (fun a => (hI2 a t).toLp (I a t)) ((hY2 t).toLp (Y t))) ∧
      (∀ T : ℝ≥0, Tendsto (fun q : Finset ι =>
        ∫ ω, MartingaleStrongMaximal.maximalSquare
          (MartingaleSpatialLimit.finiteSum I q - Y) T ω ∂P) atTop (𝓝 0)) ∧
      Martingale (fun t ω => Y t ω ^ 2 - spatialCompensator H t ω) F P ∧
      (∀ t, Integrable (spatialCompensator H t) P) ∧
      (∀ t, ∀ᵐ ω ∂P, Summable (fun a => nonnegativeCompensator (H a) t ω)) := by
  obtain ⟨I, hIp, hIM, hIc, hI2, hIz, hImean, hIiso, hIlim, hcross⟩ :=
    exists_global_continuous_channel_integrals hB hAd hpast hind hBc hH hc hC hb
  have horth (t : ℝ≥0) : Pairwise (fun a b => ∫ ω, I a t ω * I b t ω ∂P = 0) := by
    intro a b hab
    have heq := (hcross hab).setIntegral_eq
      (show (0 : ℝ≥0) ≤ t from bot_le) MeasurableSet.univ
    simp only [Measure.restrict_univ] at heq
    rw [← heq]
    calc
      _ = ∫ _ : Ω, (0 : ℝ) ∂P := by
        apply integral_congr_ae
        filter_upwards [hIz a] with ω hω
        simp only [hω, Pi.zero_apply, zero_mul]
      _ = 0 := integral_zero _ _
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
  have hAad (a : ι) := nonnegativeCompensator_stronglyAdapted (hH a)
  have hAint (a : ι) (t : ℝ≥0) :=
    nonnegativeCompensator_integrable (hH a) (hc a) (hC a) (hb a) t
  have hdiag (a : ι) :
      Martingale (fun t ω => I a t ω ^ 2 - nonnegativeCompensator (H a) t ω) F P := by
    have hQ := BrownianIntegralProcess.global_compensatedSquare_of_integer_stopped_limits
      (hB a) (hAd a) (fun s t hst => coordinate_increment_indep_past (hpast s t hst) a)
      (hH a) (hc a) (hC a) (hb a) (hIM a).stronglyAdapted (hI2 a) (hIlim a)
    apply hQ.congr (fun t => (((hIM a).stronglyAdapted t).pow 2).sub (hAad a t))
    intro t
    filter_upwards [ae_nonnegativeCompensator_eq_global (hc a)] with ω hω
    change I a t ω ^ 2 - BrownianIntegralProcess.globalCompensator (H a) t ω =
      I a t ω ^ 2 - nonnegativeCompensator (H a) t ω
    rw [hω t]
  have hAsum (t : ℝ≥0) :
      Summable (fun a => ∫ ω, nonnegativeCompensator (H a) t ω ∂P) := by
    have he := MartingaleSpatialLimit.summable_energy_of_integer hIM hI2 hIenergy t
    simpa only [integral_nonnegativeCompensator_eq_sq (hdiag _) (hI2 _) (hIz _) (hAint _)] using he
  have hQ : Martingale (fun t ω => Y t ω ^ 2 - spatialCompensator H t ω) F P :=
    MartingaleSpatialCompensator.spatial_sum_compensatedSquare_martingale hI2 hdiag hcross
      hAad hAint (fun a t ω => le_max_right _ _) hAsum hYM.stronglyAdapted hY2 hYsum
  have hseries (t : ℝ≥0) := NonnegativeSeriesL1.integrable_tsum_of_nonnegative
    (fun a => hAint a t) (fun a ω => le_max_right (BrownianIntegralProcess.globalCompensator (H a) t ω) 0)
    (hAsum t)
  exact ⟨I, Y, hI2, hY2, (fun a => ⟨hIp a, hIM a, hIc a⟩), hIlim,
    hYp, hYM, hYc, hYzero, hYiso, hYsum, hYmax, hQ,
    (fun t => (hseries t).2.1), (fun t => (hseries t).1)⟩

end Problem367.BrownianArrayFiltration

end

end OAI
