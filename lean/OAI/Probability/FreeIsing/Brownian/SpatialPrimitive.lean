import OAI.Probability.FreeIsing.Brownian.SpatialCompensator
import OAI.Probability.FreeIsing.Estimates.ProgressivePrimitive

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

def spatialSquareDensity (H : ι → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑' a, H a t ω ^ 2

omit mΩ in
theorem nonnegativeCompensator_eq_integral_of_continuous
    {H : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (fun t => H t ω)) (t : ℝ≥0) :
    nonnegativeCompensator H t ω = ∫ s in (0 : ℝ)..(t : ℝ), (H s.toNNReal ω) ^ 2 := by
  unfold nonnegativeCompensator BrownianIntegralProcess.globalCompensator
  rw [SelectedCompensator.selected_eq_integral_of_continuous hc, min_self]
  exact max_eq_left (intervalIntegral.integral_nonneg t.coe_nonneg (fun s _ => sq_nonneg _))

theorem summable_integral_sq_of_integer
    {h : ι → ℝ≥0 → ℝ} (hc : ∀ a, Continuous (h a))
    (hs : ∀ N : ℕ, Summable (fun a => ∫ s in (0 : ℝ)..(N : ℝ), (h a s.toNNReal) ^ 2))
    (t : ℝ≥0) : Summable (fun a => ∫ s in (0 : ℝ)..(t : ℝ), (h a s.toNNReal) ^ 2) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
  apply Summable.of_nonneg_of_le
    (fun a => intervalIntegral.integral_nonneg t.coe_nonneg (fun s _ => sq_nonneg _))
    (fun a => ?_) (hs N)
  have hf : Continuous (fun s : ℝ => (h a s.toNNReal) ^ 2) := by fun_prop
  exact intervalIntegral.integral_mono_interval le_rfl t.coe_nonneg hN
    (Eventually.of_forall (fun s => sq_nonneg _)) (hf.intervalIntegrable _ _)

theorem integral_spatial_sq_tsum [Countable ι]
    {h : ι → ℝ≥0 → ℝ} (hc : ∀ a, Continuous (h a))
    (hs : ∀ N : ℕ, Summable (fun a => ∫ s in (0 : ℝ)..(N : ℝ), (h a s.toNNReal) ^ 2))
    (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => ∑' a, (h a s.toNNReal) ^ 2) volume 0 (t : ℝ) ∧
      (∫ s in (0 : ℝ)..(t : ℝ), ∑' a, (h a s.toNNReal) ^ 2) =
        ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), (h a s.toNNReal) ^ 2 := by
  have hi (a : ι) : Integrable (fun s : ℝ => (h a s.toNNReal) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))) := by
    have hf : Continuous (fun s : ℝ => (h a s.toNNReal) ^ 2) := by fun_prop
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mp
      (hf.intervalIntegrable _ _)
  have hsum : Summable (fun a => ∫ s in Set.Ioc (0 : ℝ) (t : ℝ), (h a s.toNNReal) ^ 2) := by
    simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using
      summable_integral_sq_of_integer hc hs t
  obtain ⟨_, hint, heq⟩ := NonnegativeSeriesL1.integrable_tsum_of_nonnegative
    hi (fun a s => sq_nonneg _) hsum
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mpr hint,
    by simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using heq⟩

theorem ae_spatialCompensator_eq_primitive [Countable ι]
    {H : ι → ℝ≥0 → Ω → ℝ}
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (hs : ∀ N : ℕ, ∀ᵐ ω ∂P,
      Summable (fun a => nonnegativeCompensator (H a) (N : ℝ≥0) ω)) :
    ∀ᵐ ω ∂P,
      (∀ t, spatialCompensator H t ω = nnrealTimePrimitive (spatialSquareDensity H) t ω) ∧
      Continuous (fun t => nnrealTimePrimitive (spatialSquareDensity H) t ω) ∧
      (∀ t : ℝ≥0, IntervalIntegrable (fun s : ℝ => spatialSquareDensity H s.toNNReal ω)
        volume 0 (t : ℝ)) := by
  filter_upwards [ae_all_iff.mpr hc, ae_all_iff.mpr hs] with ω hcω hsω
  have hsum (N : ℕ) : Summable (fun a => ∫ s in (0 : ℝ)..(N : ℝ), (H a s.toNNReal ω) ^ 2) := by
    simpa only [nonnegativeCompensator_eq_integral_of_continuous (hcω _),
      NNReal.coe_natCast] using hsω N
  have hi (t : ℝ≥0) := integral_spatial_sq_tsum hcω hsum t
  refine ⟨?_, ?_, fun t => (hi t).1⟩
  · intro t
    change (∑' a, nonnegativeCompensator (H a) t ω) =
      ∫ s in (0 : ℝ)..(t : ℝ), ∑' a, (H a s.toNNReal ω) ^ 2
    rw [(hi t).2]
    exact tsum_congr (fun a => nonnegativeCompensator_eq_integral_of_continuous (hcω a) t)
  · exact continuous_nnreal_primitive_of_integrable_horizons _
      (fun N => by simpa only [NNReal.coe_natCast, spatialSquareDensity] using (hi (N : ℝ≥0)).1)

theorem spatialSquareDensity_isStronglyProgressive [Countable ι]
    {F : Filtration ℝ≥0 mΩ} {H : ι → ℝ≥0 → Ω → ℝ}
    (hH : ∀ a, IsStronglyProgressive F (H a)) :
    IsStronglyProgressive F (spatialSquareDensity H) := by
  intro t
  have hm (a : ι) := (hH a t).pow 2
  let : MeasurableSpace Ω := F t
  exact StronglyMeasurable.tsum hm

theorem compensatedSquare_spatial_primitive [Countable ι]
    {F : Filtration ℝ≥0 mΩ} {H : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hH : ∀ a, IsStronglyProgressive F (H a))
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (hs : ∀ N : ℕ, ∀ᵐ ω ∂P,
      Summable (fun a => nonnegativeCompensator (H a) (N : ℝ≥0) ω))
    (hY : StronglyAdapted F Y)
    (hQ : Martingale (fun t ω => Y t ω ^ 2 - spatialCompensator H t ω) F P) :
    Martingale (fun t ω => Y t ω ^ 2 - nnrealTimePrimitive (spatialSquareDensity H) t ω) F P := by
  apply hQ.congr (fun t => ((hY t).pow 2).sub
    (stronglyAdapted_nnrealTimePrimitive (spatialSquareDensity_isStronglyProgressive hH) t))
  intro t
  filter_upwards [ae_spatialCompensator_eq_primitive hc hs] with ω hω
  change Y t ω ^ 2 - spatialCompensator H t ω =
    Y t ω ^ 2 - nnrealTimePrimitive (spatialSquareDensity H) t ω
  rw [hω.1 t]

theorem integrable_spatialSquareDensity_interval [Countable ι] [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {H : ι → ℝ≥0 → Ω → ℝ}
    (hH : ∀ a, IsStronglyProgressive F (H a))
    {C : ι → ℝ} (hC : ∀ a, 0 ≤ C a)
    (hb : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
    (henergy : ∀ N : ℕ, Summable (fun a =>
      ∫ s in (0 : ℝ)..(N : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P))
    (t : ℝ≥0) :
    Integrable (fun p : ℝ × Ω => spatialSquareDensity H p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))).prod P) := by
  have hsq (a : ι) : IsStronglyProgressive F (fun t ω => H a t ω ^ 2) := by
    intro t
    exact (hH a t).pow 2
  have hi (a : ι) (N : ℕ) : Integrable (fun p : ℝ × Ω => H a p.1.toNNReal p.2 ^ 2)
      ((volume.restrict (Set.Ioc (0 : ℝ) (N : ℝ))).prod P) := by
    apply integrable_nnreal_process_interval_of_progressive_bounded (hsq a) (C a ^ 2)
      (fun r => ?_) 0 (N : ℝ≥0)
    filter_upwards [hb a] with ω hω
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hω r, hC a, abs_nonneg (H a r ω), sq_abs (H a r ω)]
  have hNint (N : ℕ) : Integrable
      (fun p : ℝ × Ω => spatialSquareDensity H p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) (N : ℝ))).prod P) := by
    have heq (a : ι) :
        (∫ p : ℝ × Ω, H a p.1.toNNReal p.2 ^ 2
          ∂((volume.restrict (Set.Ioc (0 : ℝ) (N : ℝ))).prod P)) =
        ∫ s in (0 : ℝ)..(N : ℝ), ∫ ω, H a s.toNNReal ω ^ 2 ∂P := by
      rw [integral_prod _ (hi a N), intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
    have hs : Summable (fun a => ∫ p : ℝ × Ω, H a p.1.toNNReal p.2 ^ 2
        ∂((volume.restrict (Set.Ioc (0 : ℝ) (N : ℝ))).prod P)) := by
      simpa only [heq] using henergy N
    exact (NonnegativeSeriesL1.integrable_tsum_of_nonnegative
      (fun a => hi a N) (fun a p => sq_nonneg _) hs).2.1
  obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
  exact (hNint N).mono_measure (Measure.prod_mono
    (Measure.restrict_mono (Set.Ioc_subset_Ioc le_rfl hN) le_rfl) le_rfl)

end Problem367.BrownianArrayFiltration

end

end OAI
