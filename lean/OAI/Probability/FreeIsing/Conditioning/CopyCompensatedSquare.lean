import OAI.Probability.FreeIsing.Brownian.RowComparisonConstruction
import OAI.Probability.FreeIsing.Brownian.SpatialPrimitive
import OAI.Probability.FreeIsing.Stochastic.StoppedIntegralAssociativity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem compensatedSquare_of_spatial_integral_limits
    [Countable ι] [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {B H I : ι → ℝ≥0 → Ω → ℝ}
    {Y : ℝ≥0 → Ω → ℝ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω)
        (fun ω => B b t ω - B b s ω) P)
    (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (hH : ∀ a, IsStronglyProgressive F (H a))
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    {C : ι → ℝ} (hC : ∀ a, 0 ≤ C a)
    (hb : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
    (henergy : ∀ N : ℕ, Summable (fun a =>
      ∫ s in (0 : ℝ)..(N : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P))
    (hI2 : ∀ a t, MemLp (I a t) 2 P)
    (hYad : StronglyAdapted F Y) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hlim : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω -
          I a t ω) ^ 2 ∂P) atTop (𝓝 0))
    (hsum : ∀ t, HasSum (fun a => (hI2 a t).toLp (I a t))
      ((hY2 t).toLp (Y t))) :
    Martingale Y F P ∧
      Martingale (fun t ω => Y t ω ^ 2 -
        nnrealTimePrimitive (spatialSquareDensity H) t ω) F P := by
  obtain ⟨J, Z, hJ2, hZ2, hJ, hJlim, hZp, hZM, hZc, hZ0,
      hZiso, hZsum, hZmax, hZQ, hZA, hZseries⟩ :=
    exists_global_continuous_spatial_integral_compensatedSquare
      hB hAd hpast hind hBc (fun a => (hH a).stronglyAdapted)
      hc hC hb henergy
  have hIJ (a : ι) (t : ℝ≥0) : I a t =ᵐ[P] J a t := by
    obtain ⟨N, htN⟩ := exists_nat_gt (t : ℝ)
    have hN : 0 < N := by exact_mod_cast (t.coe_nonneg.trans_lt htN)
    have htN' : t ≤ (N : ℝ≥0) := by exact_mod_cast htN.le
    apply BrownianGrid.ae_eq_of_mean_square_limits
      (fun n => StoppedIntegralAssociativity.stoppedUniformSum_memLp
        (fun s => (hB a).isGaussianProcess.hasGaussianLaw_eval s |>.memLp_two)
        (hH a).stronglyAdapted (hb a) (N : ℝ≥0) n t)
      (hI2 a t) (hJ2 a t)
    · exact hlim a N hN t htN'
    · exact hJlim a N hN t htN'
  have hYZ (t : ℝ≥0) : Y t =ᵐ[P] Z t := by
    have heq : (fun a => (hI2 a t).toLp (I a t)) =
        (fun a => (hJ2 a t).toLp (J a t)) :=
      funext (fun a => MemLp.toLp_congr (hI2 a t) (hJ2 a t) (hIJ a t))
    have hs := hsum t
    rw [heq] at hs
    exact (MemLp.toLp_eq_toLp_iff (hY2 t) (hZ2 t)).mp (hs.unique (hZsum t))
  have hQ := compensatedSquare_spatial_primitive hH hc
    (fun N => hZseries (N : ℝ≥0)) hZM.stronglyAdapted hZQ
  refine ⟨hZM.congr hYad (fun t => (hYZ t).symm), ?_⟩
  apply hQ.congr (fun t => ((hYad t).pow 2).sub
    (stronglyAdapted_nnrealTimePrimitive (spatialSquareDensity_isStronglyProgressive hH) t))
  intro t
  filter_upwards [hYZ t] with ω hω
  exact congrArg (fun z => z ^ 2 - nnrealTimePrimitive (spatialSquareDensity H) t ω) hω.symm

theorem difference_compensatedSquare_of_spatial_integral_limits
    [Countable ι] [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {B H K I J : ι → ℝ≥0 → Ω → ℝ}
    {Y Z : ℝ≥0 → Ω → ℝ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hpast : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hind : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω)
        (fun ω => B b t ω - B b s ω) P)
    (hBc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => B a t ω))
    (hH : ∀ a, IsStronglyProgressive F (H a))
    (hK : ∀ a, IsStronglyProgressive F (K a))
    (hcH : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (hcK : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => K a t ω))
    {C D : ι → ℝ} (hC : ∀ a, 0 ≤ C a) (hD : ∀ a, 0 ≤ D a)
    (hbH : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
    (hbK : ∀ a, ∀ᵐ ω ∂P, ∀ t, |K a t ω| ≤ D a)
    (heH : ∀ N : ℕ, Summable (fun a =>
      ∫ s in (0 : ℝ)..(N : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P))
    (heK : ∀ N : ℕ, Summable (fun a =>
      ∫ s in (0 : ℝ)..(N : ℝ), ∫ ω, K a s.toNNReal ω ^ 2 ∂P))
    (hI2 : ∀ a t, MemLp (I a t) 2 P) (hJ2 : ∀ a t, MemLp (J a t) 2 P)
    (hYad : StronglyAdapted F Y) (hZad : StronglyAdapted F Z)
    (hY2 : ∀ t, MemLp (Y t) 2 P) (hZ2 : ∀ t, MemLp (Z t) 2 P)
    (hlimI : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω -
          I a t ω) ^ 2 ∂P) atTop (𝓝 0))
    (hlimJ : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ ω,
        (BrownianIntegralProcess.stoppedUniformSum (B a) (K a) N n t ω -
          J a t ω) ^ 2 ∂P) atTop (𝓝 0))
    (hsY : ∀ t, HasSum (fun a => (hI2 a t).toLp (I a t))
      ((hY2 t).toLp (Y t)))
    (hsZ : ∀ t, HasSum (fun a => (hJ2 a t).toLp (J a t))
      ((hZ2 t).toLp (Z t))) :
    Martingale (fun t ω => Y t ω - Z t ω) F P ∧
      Martingale (fun t ω => (Y t ω - Z t ω) ^ 2 -
        nnrealTimePrimitive
          (spatialSquareDensity (fun a t ω => H a t ω - K a t ω)) t ω) F P := by
  have hc (a : ι) : ∀ᵐ ω ∂P, Continuous (fun t => H a t ω - K a t ω) := by
    filter_upwards [hcH a, hcK a] with ω hω kω
    exact hω.sub kω
  have hb (a : ι) : ∀ᵐ ω ∂P, ∀ t, |H a t ω - K a t ω| ≤ C a + D a := by
    filter_upwards [hbH a, hbK a] with ω hω kω
    exact fun t => (abs_sub _ _).trans (add_le_add (hω t) (kω t))
  have he (N : ℕ) : Summable (fun a => ∫ s in (0 : ℝ)..(N : ℝ),
      ∫ ω, (H a s.toNNReal ω - K a s.toNNReal ω) ^ 2 ∂P) := by
    by_cases hN : 0 < N
    · apply summable_difference_energy_of_row_energies hB hAd hpast H K
        (fun a => (hH a).stronglyAdapted) (fun a => (hK a).stronglyAdapted)
        hcH hcK C D hC hD hbH hbK (N : ℝ≥0) (heH N) (heK N)
        (fun a => hI2 a N) (fun a => hJ2 a N)
      · intro a
        simpa only [BrownianIntegralProcess.stoppedUniformSum_terminal] using
          hlimI a N hN N le_rfl
      · intro a
        simpa only [BrownianIntegralProcess.stoppedUniformSum_terminal] using
          hlimJ a N hN N le_rfl
    · have hn : N = 0 := Nat.eq_zero_of_not_pos hN
      simp only [hn, Nat.cast_zero, intervalIntegral.integral_same]
      exact summable_zero
  apply compensatedSquare_of_spatial_integral_limits hB hAd hpast hind hBc
    (fun a t => (hH a t).sub (hK a t)) hc (fun a => add_nonneg (hC a) (hD a)) hb he
    (fun a t => (hI2 a t).sub (hJ2 a t))
    (fun t => (hYad t).sub (hZad t)) (fun t => (hY2 t).sub (hZ2 t))
  · intro a N hN t htN
    have hM2 (s : ℝ≥0) := (hB a).isGaussianProcess.hasGaussianLaw_eval s |>.memLp_two
    have h := SimpleIntegral.meanSquare_limit_sub
      (fun n => StoppedIntegralAssociativity.stoppedUniformSum_memLp
        hM2 (hH a).stronglyAdapted (hbH a) N n t)
      (fun n => StoppedIntegralAssociativity.stoppedUniformSum_memLp
        hM2 (hK a).stronglyAdapted (hbK a) N n t)
      (hI2 a t) (hJ2 a t) (hlimI a N hN t htN) (hlimJ a N hN t htN)
    have heq (n : ℕ) (ω : Ω) :
        BrownianIntegralProcess.stoppedUniformSum (B a)
          (fun s ω => H a s ω - K a s ω) N n t ω =
        BrownianIntegralProcess.stoppedUniformSum (B a) (H a) N n t ω -
          BrownianIntegralProcess.stoppedUniformSum (B a) (K a) N n t ω := by
      simp only [BrownianIntegralProcess.stoppedUniformSum,
        StoppedSimpleIntegral.intervalSum, sub_mul, Finset.sum_sub_distrib]
    simpa only [heq, Pi.sub_apply] using h
  · intro t
    exact (hsY t).sub (hsZ t)

end Problem367.BrownianArrayFiltration

end

end OAI
