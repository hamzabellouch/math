import OAI.Probability.FreeIsing.Martingales.L2MartingaleRightContinuation
import OAI.Probability.FreeIsing.Martingales.SpatialRandomEvaluation
import OAI.Probability.FreeIsing.Stochastic.StoppedIntegralLocality

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.StoppedRowNormalization
open BrownianGrid BrownianIntegralProcess DominatedMartingaleRightContinuation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem stopped_channel_normalization
    {F : Filtration ℝ≥0 mΩ} {B C R K I J : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hcB : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hC : StronglyAdapted F C) (hR : StronglyAdapted F R) (hK : StronglyAdapted F K)
    (hcC : ∀ᵐ ω ∂P, Continuous (fun t => C t ω))
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hbC : ∀ᵐ ω ∂P, ∀ t, |C t ω| ≤ a)
    (hbR : ∀ᵐ ω ∂P, ∀ t, |R t ω| ≤ b)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ c)
    (hI : Martingale I F P) (hJ : Martingale J F P)
    (hI2 : ∀ t, MemLp (I t) 2 P) (hJ2 : ∀ t, MemLp (J t) 2 P)
    (hcI : ∀ᵐ ω ∂P, Continuous (fun t => I t ω))
    (hcJ : ∀ᵐ ω ∂P, Continuous (fun t => J t ω))
    (T : ℝ≥0)
    (hIlim : Tendsto (fun n => ∫ ω,
      (uniformSum B C T n ω - I T ω) ^ 2 ∂P) atTop (𝓝 0))
    (hJlim : Tendsto (fun n => ∫ ω,
      (uniformSum B R T n ω - J T ω) ^ 2 ∂P) atTop (𝓝 0))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ)
    (hlocal : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω →
      K t ω * C t ω = R t ω) :
    Tendsto (fun n => ∫ ω,
      (uniformSum (stoppedProcess I τ) K T n ω - stoppedProcess J τ T ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hKC : StronglyAdapted F (fun t ω => K t ω * C t ω) :=
    fun t => (hK t).mul (hC t)
  have hcKC : ∀ᵐ ω ∂P, Continuous (fun t => K t ω * C t ω) :=
    (hcK.and hcC).mono (fun ω hω => hω.1.mul hω.2)
  have hbKC : ∀ᵐ ω ∂P, ∀ t, |K t ω * C t ω| ≤ c * a := by
    filter_upwards [hbK, hbC] with ω hk hcω
    intro t
    exact (abs_mul _ _).trans_le (mul_le_mul (hk t) (hcω t) (abs_nonneg _) hc)
  obtain ⟨L, hLp, hL, hcL, hL2, _, _, _, _, hLlim⟩ :=
    exists_continuous_stopped_uniform_integral hB hAd hind hcB hKC hcKC
      (mul_nonneg hc ha) hbKC T
  have hLterminal : Tendsto (fun n => ∫ ω,
      (uniformSum B (fun t ω => K t ω * C t ω) T n ω - L T ω) ^ 2 ∂P)
        atTop (𝓝 0) := by
    simpa only [stoppedUniformSum_terminal] using hLlim T
  have houter := BrownianContinuousAssociativity.uniformSum_associativity
    hB hAd hind hC hK hcK ha hc hbC hbK hI hI2 T hIlim (hL2 T) hLterminal
  have hIright := martingale_rightCont_of_ae_continuous_memLp_two hI hI2 hcI
  have hJright := martingale_rightCont_of_ae_continuous_memLp_two hJ hJ2 hcJ
  have hLright := martingale_rightCont_of_ae_continuous_memLp_two hL hL2 hcL
  have hKright : StronglyAdapted F.rightCont K :=
    fun t => (hK t).mono (F.le_rightCont t)
  have hstop := StoppedIntegralAssociativity.tendsto_stopped_outer_uniformSum
    hIright hI2 hcI hKright hbK hLright hL2 hcL T houter hτ
  have hBM := BrownianFiltration.martingale_of_independent_past hB hAd hind
  have hB2 (t : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hBright := martingale_rightCont_of_ae_continuous_memLp_two hBM hB2 hcB
  have heq := StoppedIntegralLocality.stopped_integral_eq_of_local_eq
    hBright hB2 hcB (fun t => (hKC t).mono (F.le_rightCont t))
    (fun t => (hR t).mono (F.le_rightCont t)) hbKC hbR
    hLright hJright hL2 hJ2 hcL hcJ T hLterminal hJlim hτ hlocal
  apply hstop.congr
  intro n
  apply integral_congr_ae
  filter_upwards [heq] with ω hω
  rw [hω]

theorem stopped_row_normalization {ι : Type*} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {B C R I J : ι → ℝ≥0 → Ω → ℝ}
    {M Z K : ℝ≥0 → Ω → ℝ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ a s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcB : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (hC : ∀ a, StronglyAdapted F (C a)) (hR : ∀ a, StronglyAdapted F (R a))
    (hK : StronglyAdapted F K)
    (hcC : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => C a t ω))
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {c r : ι → ℝ} {k : ℝ} (hc : ∀ a, 0 ≤ c a) (hk : 0 ≤ k)
    (hbC : ∀ a, ∀ᵐ ω ∂P, ∀ t, |C a t ω| ≤ c a)
    (hbR : ∀ a, ∀ᵐ ω ∂P, ∀ t, |R a t ω| ≤ r a)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ k)
    (hI : ∀ a, Martingale (I a) F P) (hJ : ∀ a, Martingale (J a) F P)
    (hM : Martingale M F P) (hZ : Martingale Z F P)
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hJ2 : ∀ a t, MemLp (J a t) 2 P)
    (hM2 : ∀ t, MemLp (M t) 2 P) (hZ2 : ∀ t, MemLp (Z t) 2 P)
    (hcI : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => I a t ω))
    (hcJ : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => J a t ω))
    (hcM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hcZ : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω))
    (hpI : ∀ a, IsStronglyProgressive F (I a)) (hpM : IsStronglyProgressive F M)
    (T : ℝ≥0)
    (hsumI : HasSum (fun a => (hI2 a T).toLp (I a T)) ((hM2 T).toLp (M T)))
    (hsumJ : HasSum (fun a => (hJ2 a T).toLp (J a T)) ((hZ2 T).toLp (Z T)))
    (hIlim : ∀ a, Tendsto (fun n => ∫ ω,
      (uniformSum (B a) (C a) T n ω - I a T ω) ^ 2 ∂P) atTop (𝓝 0))
    (hJlim : ∀ a, Tendsto (fun n => ∫ ω,
      (uniformSum (B a) (R a) T n ω - J a T ω) ^ 2 ∂P) atTop (𝓝 0))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ)
    (hlocal : ∀ a, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω →
      K t ω * C a t ω = R a t ω) :
    Tendsto (fun n => ∫ ω,
      (uniformSum (stoppedProcess M τ) K T n ω - stoppedProcess Z τ T ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hIr (a : ι) := martingale_rightCont_of_ae_continuous_memLp_two (hI a) (hI2 a) (hcI a)
  have hJr (a : ι) := martingale_rightCont_of_ae_continuous_memLp_two (hJ a) (hJ2 a) (hcJ a)
  have hMr := martingale_rightCont_of_ae_continuous_memLp_two hM hM2 hcM
  have hZr := martingale_rightCont_of_ae_continuous_memLp_two hZ hZ2 hcZ
  have hIs (a : ι) := martingale_stoppedProcess_rightCont_of_memLp_two
    (hI a) (hI2 a) (hpI a) (hcI a) hτ
  have hMs := martingale_stoppedProcess_rightCont_of_memLp_two hM hM2 hpM hcM hτ
  have hIs2 (a : ι) (t : ℝ≥0) :=
    StoppedMartingaleL2.memLp_stoppedProcess_two (hIr a) (hI2 a) (hcI a) hτ t
  have hMs2 (t : ℝ≥0) :=
    StoppedMartingaleL2.memLp_stoppedProcess_two hMr hM2 hcM hτ t
  obtain ⟨hIsT, hMsT, hsI⟩ :=
    MartingaleSpatialRandomEvaluation.exists_hasSum_stoppedProcess hIr hMr hI2 hM2
      hcI hcM T hsumI hτ (t := T) le_rfl
  obtain ⟨hJsT, hZsT, hsJ⟩ :=
    MartingaleSpatialRandomEvaluation.exists_hasSum_stoppedProcess hJr hZr hJ2 hZ2
      hcJ hcZ T hsumJ hτ (t := T) le_rfl
  apply BrownianSpatialAssociativity.uniformSum_spatial_limit_of_channel_limits
    hIs hMs hIs2 hMs2 hJsT hZsT (fun t => (hK t).mono (F.le_rightCont t)) hk
    (fun t => hbK.mono (fun ω hω => hω t)) T hsI hsJ
  intro a
  exact stopped_channel_normalization (hB a) (hAd a) (hind a) (hcB a)
    (hC a) (hR a) hK (hcC a) hcK (hc a) hk (hbC a) (hbR a) hbK
    (hI a) (hJ a) (hI2 a) (hJ2 a) (hcI a) (hcJ a) T (hIlim a) (hJlim a)
    hτ (hlocal a)

end Problem367.StoppedRowNormalization

end

end OAI
