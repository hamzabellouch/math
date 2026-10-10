import OAI.Probability.FreeIsing.Brownian.ContinuousIntegral
import OAI.Probability.FreeIsing.Martingales.StoppedEnergyRiemann

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem L2_tendsto_of_integral_sq_sub_tendsto
    {X : ℕ → Ω → ℝ} {L : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hL : MemLp L 2 P)
    (hlim : Tendsto (fun n => ∫ ω, (X n ω - L ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 (hL.toLp L)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hsq : Tendsto (fun n => dist ((hX n).toLp (X n)) (hL.toLp L) ^ 2)
      atTop (𝓝 0) := by
    simpa only [MartingaleSquareMaximal.dist_toLp_sq] using hlim
  have hsqrt := hsq.sqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg, Real.sqrt_zero] using hsqrt

theorem norm_toLp_sq_eq_integral {X : Ω → ℝ} (hX : MemLp X 2 P) :
    ‖hX.toLp X‖ ^ 2 = ∫ ω, X ω ^ 2 ∂P := by
  rw [BrownianGrid.norm_sq_L2_eq_integral]
  apply integral_congr_ae
  filter_upwards [hX.coeFn_toLp] with ω hω
  rw [hω]

theorem integral_sq_tendsto_of_meanSquare
    {X : ℕ → Ω → ℝ} {L : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hL : MemLp L 2 P)
    (hlim : Tendsto (fun n => ∫ ω, (X n ω - L ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, X n ω ^ 2 ∂P) atTop (𝓝 (∫ ω, L ω ^ 2 ∂P)) := by
  have hnorm := (L2_tendsto_of_integral_sq_sub_tendsto hX hL hlim).norm.pow 2
  simpa only [norm_toLp_sq_eq_integral] using hnorm

theorem stopped_uniform_limit_isometry
    {B H : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T t : ℝ≥0) {I : Ω → ℝ} (hI : MemLp I 2 P)
    (hlim : Tendsto (fun n => ∫ ω,
      (stoppedUniformSum B H T n t ω - I ω) ^ 2 ∂P) atTop (𝓝 0)) :
    (∫ ω, I ω ^ 2 ∂P) =
      ∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), ∫ ω, (H s.toNNReal ω) ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (r : ℝ≥0) : MemLp (H r) 2 P := by
    apply MemLp.of_bound ((hH r).mono (F.le r)).aestronglyMeasurable C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω r
  have hS2 (n : ℕ) : MemLp (stoppedUniformSum B H T n t) 2 P :=
    BrownianFiltration.stopped_predictable_sum_memLp_two hB hind
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun i => H (BrownianGrid.uniformGrid T n i)) (fun i => hH _) (fun i => hH2 _)
      (Finset.range n) t
  have henergy := EnergyRiemann.tendsto_stopped_energy_sum
    (fun r => (hH2 r).aestronglyMeasurable) hc hC hb T t
  have hiso (n : ℕ) := BrownianFiltration.stopped_predictable_sum_isometry hB hAd hind
    (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
    (fun i => H (BrownianGrid.uniformGrid T n i)) (fun i => hH _) (fun i => hH2 _)
    (Finset.range n) t
  have he : Tendsto (fun n => ∫ ω, stoppedUniformSum B H T n t ω ^ 2 ∂P) atTop
      (𝓝 (∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), ∫ ω, (H s.toNNReal ω) ^ 2 ∂P)) := by
    apply henergy.congr'
    apply Filter.Eventually.of_forall
    intro n
    exact (hiso n).symm
  exact tendsto_nhds_unique (integral_sq_tendsto_of_meanSquare hS2 hI hlim) he

theorem exists_continuous_stopped_uniform_integral_isometry
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
      (∀ t, (∫ ω, (I t ω) ^ 2 ∂P) =
        ∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), ∫ ω, (H s.toNNReal ω) ^ 2 ∂P) ∧
      (∀ t, Tendsto (fun n => ∫ ω,
        (stoppedUniformSum B H T n t ω - I t ω) ^ 2 ∂P) atTop (𝓝 0)) := by
  obtain ⟨I, hp, hM, hcont, hI2, hzero, hmean, hstop, _, hlim⟩ :=
    exists_continuous_stopped_uniform_integral hB hAd hind hBc hH hc hC hb T
  exact ⟨I, hp, hM, hcont, hI2, hzero, hmean, hstop,
    (fun t => stopped_uniform_limit_isometry hB hAd hind hH hc hC hb T t (hI2 t) (hlim t)), hlim⟩

end Problem367.BrownianIntegralProcess

end

end OAI
