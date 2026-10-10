import OAI.Probability.FreeIsing.Brownian.IntegralContinuitySupport
import OAI.Probability.FreeIsing.Martingales.L2Closure

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

omit mΩ in
theorem stoppedUniformSum_terminal (B H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) :
    stoppedUniformSum B H T n T = BrownianGrid.uniformSum B H T n := by
  funext ω
  unfold stoppedUniformSum BrownianGrid.uniformSum BrownianGrid.integralSum
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i) hin
  have ha := BrownianGrid.uniformGrid_le_horizon T hn hin.le
  have hb := BrownianGrid.uniformGrid_le_horizon T hn hin
  simp only [StoppedSimpleIntegral.intervalSum, min_eq_right ha, min_eq_right hb]

theorem integral_sq_sub_tendsto_of_L2_tendsto
    {X : ℕ → Ω → ℝ} {L : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hL : MemLp L 2 P)
    (hlim : Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 (hL.toLp L))) :
    Tendsto (fun n => ∫ ω, (X n ω - L ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hdist := (tendsto_iff_dist_tendsto_zero.mp hlim).pow 2
  simpa only [MartingaleSquareMaximal.dist_toLp_sq, zero_pow (by decide : 2 ≠ 0)] using hdist

theorem exists_continuous_stopped_uniform_integral
    {B H : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hBc : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hH : StronglyAdapted F H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C) (T : ℝ≥0) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F I ∧ Martingale I F P ∧
      (∀ᵐ ω ∂P, Continuous (fun t => I t ω)) ∧
      (∀ t, MemLp (I t) 2 P) ∧ I 0 =ᵐ[P] 0 ∧
      (∀ t, (∫ ω, I t ω ∂P) = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, T ≤ t → I t ω = I T ω) ∧
      (∫ ω, (I T ω) ^ 2 ∂P) =
        (∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, (H t.toNNReal ω) ^ 2 ∂P) ∧
      (∀ t, Tendsto (fun n => ∫ ω,
        (stoppedUniformSum B H T n t ω - I t ω) ^ 2 ∂P) atTop (𝓝 0)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P := by
    apply MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hS2 (n : ℕ) (t : ℝ≥0) : MemLp (stoppedUniformSum B H T n t) 2 P :=
    BrownianFiltration.stopped_predictable_sum_memLp_two hB hind
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun i => H (BrownianGrid.uniformGrid T n i)) (fun i => hH _) (fun i => hH2 _)
      (Finset.range n) t
  have hSM (n : ℕ) : Martingale (stoppedUniformSum B H T n) F P := by
    apply BrownianFiltration.stopped_predictable_sum_martingale hB hAd hind
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun i => H (BrownianGrid.uniformGrid T n i)) (fun i => hH _) (fun _ => C)
      (fun i => ?_) (Finset.range n)
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω (BrownianGrid.uniformGrid T n i)
  have hSC : CauchySeq (fun n => (hS2 n T).toLp (stoppedUniformSum B H T n T)) := by
    have hclass : (fun n => (hS2 n T).toLp (stoppedUniformSum B H T n T)) =
        BrownianFiltrationGrid.uniformSumLp hB hAd hind H hH hH2 T := by
      funext n
      apply Lp.ext
      exact (hS2 n T).coeFn_toLp.trans
        ((stoppedUniformSum_terminal B H T n).eventuallyEq.trans
          (BrownianFiltrationGrid.coe_uniformSumLp hB hAd hind H hH hH2 T n).symm)
    rw [hclass]
    exact BrownianFiltrationGrid.cauchySeq_uniformSumLp hB hAd hind H hH hH2 T
      (fun ε hε => MeanSquareContinuity.uniform_integral_sq_sub_le
        (fun t => (hH2 t).aestronglyMeasurable) hc hC hb T hε)
  obtain ⟨L, hLp, hLc, hLlim⟩ :=
    MartingaleSquareMaximal.exists_predictable_continuous_L2_limit hSM hS2
      (ae_continuous_stoppedUniformSum hBc T) T hSC
  obtain ⟨M, hM, hM2, hMzero, hMstop, hMiso, hMlim⟩ :=
    exists_stopped_uniform_integral_process hB hAd hind hH hc hC hb T
  have hLM (t : ℝ≥0) (ht : t ≤ T) : L t =ᵐ[P] M t := by
    obtain ⟨hL2, hlim⟩ := hLlim t ht
    exact BrownianGrid.ae_eq_of_mean_square_limits (fun n => hS2 n t) hL2 (hM2 t)
      (integral_sq_sub_tendsto_of_L2_tendsto (fun n => hS2 n t) hL2 hlim) (hMlim t)
  let R : ℝ≥0 → Ω → ℝ := fun t => L (min t T)
  have hRad : StronglyAdapted F R := fun t =>
    (hLp.stronglyAdapted (min t T)).mono (F.mono (min_le_left _ _))
  have hRc : ∀ᵐ ω ∂P, Continuous (fun t => R t ω) := by
    filter_upwards [hLc] with ω hω
    exact hω.comp_continuous (continuous_id.min continuous_const) (fun t => min_le_right t T)
  let I := PredictableMesh.repair R
  have hIp : IsStronglyPredictable F I := PredictableMesh.repair_isStronglyPredictable hRad
  have hIR : ∀ᵐ ω ∂P, ∀ t, I t ω = R t ω := by
    filter_upwards [hRc] with ω hω
    intro t
    exact PredictableMesh.repair_eq_of_continuousOn (T := t) hω.continuousOn le_rfl
  have hIM (t : ℝ≥0) : I t =ᵐ[P] M t := by
    filter_upwards [hIR, hLM (min t T) (min_le_right _ _)] with ω hIω hω
    rw [hIω t]
    change L (min t T) ω = M t ω
    rw [hω]
    by_cases ht : t ≤ T
    · rw [min_eq_left ht]
    · rw [min_eq_right (le_of_not_ge ht), hMstop t (le_of_not_ge ht)]
  refine ⟨I, hIp, hM.congr hIp.stronglyAdapted (fun t => (hIM t).symm), ?_,
    (fun t => (hM2 t).ae_eq (hIM t).symm), ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hIR, hRc] with ω hIω hω
    exact hω.congr (fun t => (hIω t).symm)
  · exact (hIM 0).trans (initial_zero_of_stopped_uniform_limit T (hM2 0) (hMlim 0))
  · intro t
    exact (integral_congr_ae (hIM t)).trans (hMzero t)
  · filter_upwards [hIR] with ω hω
    intro t ht
    rw [hω t, hω T]
    dsimp [R]
    rw [min_eq_right ht, min_self]
  · rw [← hMiso]
    apply integral_congr_ae
    filter_upwards [hIM T] with ω hω
    rw [hω]
  · intro t
    apply (hMlim t).congr'
    apply Filter.Eventually.of_forall
    intro n
    apply integral_congr_ae
    filter_upwards [hIM t] with ω hω
    rw [hω]

end Problem367.BrownianIntegralProcess

end

end OAI
