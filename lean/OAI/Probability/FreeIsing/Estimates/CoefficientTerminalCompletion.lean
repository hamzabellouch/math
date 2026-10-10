import OAI.Probability.FreeIsing.Brownian.RowEnergyCompletion
import OAI.Probability.FreeIsing.Posterior.FilteringRepresentationClosure

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.FilteringRepresentationClosure

theorem meanSquare_cauchy_of_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hY : MemLp Y 2 P)
    (hlim : Tendsto (fun n => ∫ ω, (X n ω - Y ω) ^ 2 ∂P) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
      (∫ ω, (X n ω - X k ω) ^ 2 ∂P) < ε := by
  have hc := (tendsto_toLp_of_integral_sq_error hX hY hlim).cauchySeq
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (Real.sqrt ε) (Real.sqrt_pos.2 hε)
  refine ⟨N, fun n hn k hk => ?_⟩
  have hd := hN n hn k hk
  have he : (∫ ω, (X n ω - X k ω) ^ 2 ∂P) =
      dist ((hX n).toLp (X n)) ((hX k).toLp (X k)) ^ 2 := by
    rw [dist_eq_norm]
    exact (PredictableL2.norm_toLp_sq ((hX n).sub (hX k))).symm
  rw [he]
  have hs := Real.sq_sqrt hε.le
  nlinarith [dist_nonneg (x := (hX n).toLp (X n)) (y := (hX k).toLp (X k)),
    Real.sqrt_nonneg ε]

theorem exists_terminal_limit_of_coefficient_approximation
    {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} [IsFiniteMeasure P] {Q : Measure Ξ}
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    {M : Ω → ℝ} (hM : MemLp M 2 P)
    (X : ℕ → Ω → ℝ) (G : ℕ → Ξ → ℝ) (C : Ξ → ℝ)
    (hX : ∀ n, MemLp (X n) 2 P)
    (htX : ∀ n, AEStronglyMeasurable[F T] (X n) P)
    (hzX : ∀ n, (∫ ω, X n ω ∂P) = 0)
    (hG : ∀ n, MemLp (G n) 2 Q) (hC : MemLp C 2 Q)
    (hGlim : Tendsto (fun n => ∫ ξ, (G n ξ - C ξ) ^ 2 ∂Q) atTop (𝓝 0))
    (hpair : ∀ n k, (∫ ω, (X n ω - X k ω) ^ 2 ∂P) =
      ∫ ξ, (G n ξ - G k ξ) ^ 2 ∂Q)
    (hiso : ∀ n, (∫ ω, X n ω ^ 2 ∂P) = ∫ ξ, G n ξ ^ 2 ∂Q)
    (htest : ∀ n, (∫ ω, M ω * X n ω ∂P) = ∫ ξ, C ξ * G n ξ ∂Q) :
    ∃ Y : Ω → ℝ, Measurable Y ∧ AEStronglyMeasurable[F T] Y P ∧
      MemLp Y 2 P ∧ (∫ ω, Y ω ∂P) = 0 ∧
      Tendsto (fun n => ∫ ω, (X n ω - Y ω) ^ 2 ∂P) atTop (𝓝 0) ∧
      (∫ ω, Y ω ^ 2 ∂P) = (∫ ξ, C ξ ^ 2 ∂Q) ∧
      (∫ ω, M ω * Y ω ∂P) = (∫ ξ, C ξ ^ 2 ∂Q) := by
  have hc : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
      (∫ ω, (X n ω - X k ω) ^ 2 ∂P) < ε := by
    simpa only [hpair] using meanSquare_cauchy_of_tendsto hG hC hGlim
  obtain ⟨Y, hmY, htY, hY, hzY, haY, heY⟩ :=
    PredictableL2.exists_centered_terminal_meanSquare_limit F T X hX htX hzX hc
  have hg := tendsto_toLp_of_integral_sq_error hG hC hGlim
  refine ⟨Y, hmY, htY, hY, hzY, haY, ?_, ?_⟩
  · have heC := hg.norm.pow 2
    simp only [PredictableL2.norm_toLp_sq] at heC
    exact tendsto_nhds_unique (by simpa only [hiso] using heY) heC
  · have h := cross_energy_of_approximations (hM.toLp M) (hY.toLp Y) (hC.toLp C)
      (fun n => (hX n).toLp (X n)) (fun n => (hG n).toLp (G n))
      (tendsto_toLp_of_integral_sq_error hX hY haY) hg
      (Eventually.of_forall (fun n => by simpa only [PredictableL2.inner_toLp] using htest n))
    simpa only [PredictableL2.inner_toLp, PredictableL2.norm_toLp_sq] using h

theorem pairwise_orthogonal_of_meanSquare_limits
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → ι → Ω → ℝ} {Y : ι → Ω → ℝ}
    (hX : ∀ n i, MemLp (X n i) 2 P) (hY : ∀ i, MemLp (Y i) 2 P)
    (hlim : ∀ i, Tendsto (fun n => ∫ ω, (X n i ω - Y i ω) ^ 2 ∂P)
      atTop (𝓝 0))
    (horth : ∀ n, Pairwise fun i j => ∫ ω, X n i ω * X n j ω ∂P = 0) :
    Pairwise fun i j => ∫ ω, Y i ω * Y j ω ∂P = 0 := by
  intro i j hij
  have hi := tendsto_toLp_of_integral_sq_error (fun n => hX n i) (hY i) (hlim i)
  have hj := tendsto_toLp_of_integral_sq_error (fun n => hX n j) (hY j) (hlim j)
  have h := hi.inner (𝕜 := ℝ) hj
  simp only [PredictableL2.inner_toLp] at h
  exact tendsto_nhds_unique h (by simpa only [horth _ hij] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))

end Problem367.FilteringRepresentationClosure

end

end OAI
