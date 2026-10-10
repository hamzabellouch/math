import OAI.Probability.FreeIsing.Brownian.IntegralProperties
import OAI.Probability.FreeIsing.Energy.EnergyRiemannApproximation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianGrid

lemma uniformGrid_step (T : ℝ≥0) (n i : ℕ) :
    (uniformGrid T n (i + 1) : ℝ) - (uniformGrid T n i : ℝ) = (T : ℝ) / n := by
  simp only [uniformGrid, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
    Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
  ring

theorem uniformSumLp_norm_sq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (Filtration.natural B hm) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0) (n : ℕ) :
    ‖uniformSumLp hB hm H hH hH2 T n‖ ^ 2 =
      ((T : ℝ) / n) * ∑ i ∈ Finset.range n, ∫ ω, (H (uniformGrid T n i) ω) ^ 2 ∂P := by
  calc
    _ = ∫ ω, (uniformSum B H T n ω) ^ 2 ∂P := by
      rw [norm_sq_L2_eq_integral]
      apply integral_congr_ae
      filter_upwards [coe_uniformSumLp hB hm H hH hH2 T n] with ω hω
      rw [hω]
    _ = ∑ i ∈ Finset.range n,
        ((uniformGrid T n (i + 1) : ℝ) - (uniformGrid T n i : ℝ)) *
          ∫ ω, (H (uniformGrid T n i) ω) ^ 2 ∂P :=
      preBrownian_predictable_sum_isometry hB hm (uniformGrid T n) (uniformGrid_mono T n)
        (fun i => H (uniformGrid T n i)) (fun i => hH _) (fun i => hH2 _) (Finset.range n)
    _ = _ := by simp_rw [uniformGrid_step]; rw [← Finset.mul_sum]

theorem uniformSumLp_limit_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (Filtration.natural B hm) H)
    (hH2 : ∀ t, MemLp (H t) 2 P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T : ℝ≥0) {I : Lp ℝ 2 P}
    (hI : Tendsto (uniformSumLp hB hm H hH hH2 T) atTop (𝓝 I)) :
    (∫ ω, (I ω) ^ 2 ∂P) =
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, (H t.toNNReal ω) ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have henergy := EnergyRiemann.tendsto_energy_sum
    (fun t => (hH2 t).aestronglyMeasurable) hc hC hb T
  have hnorm := hI.norm.pow 2
  have henergy' : Tendsto
      (fun n => ((T : ℝ) / n) * ∑ i ∈ Finset.range n,
        ∫ ω, (H (uniformGrid T n i) ω) ^ 2 ∂P) atTop (𝓝 (‖I‖ ^ 2)) := by
    apply hnorm.congr'
    exact Filter.Eventually.of_forall (uniformSumLp_norm_sq hB hm H hH hH2 T)
  rw [← norm_sq_L2_eq_integral]
  exact tendsto_nhds_unique henergy' henergy

theorem exists_terminal_uniform_integral_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (Filtration.natural B hm) H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T : ℝ≥0) :
    ∃ I : Ω → ℝ, StronglyMeasurable[Filtration.natural B hm T] I ∧ MemLp I 2 P ∧
      (∫ ω, I ω ∂P) = 0 ∧
      (∫ ω, (I ω) ^ 2 ∂P) = (∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, (H t.toNNReal ω) ^ 2 ∂P) ∧
      Tendsto (fun n => ∫ ω, (uniformSum B H T n ω - I ω) ^ 2 ∂P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hHm : ∀ t, AEStronglyMeasurable (H t) P := fun t =>
    ((hH t).mono ((Filtration.natural B hm).le t)).aestronglyMeasurable
  have hH2 : ∀ t, MemLp (H t) 2 P := by
    intro t
    apply MemLp.of_bound (hHm t) C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  obtain ⟨I, hI⟩ := exists_uniformSumLp_limit hB hm H hH hH2 T
    (fun _ hε => MeanSquareContinuity.uniform_integral_sq_sub_le hHm hc hC hb T hε)
  obtain ⟨hIm, hIzero⟩ := uniformSumLp_limit_terminal_centered hB hm H hH hH2 T hI
  have hiso := uniformSumLp_limit_isometry hB hm H hH hH2 hc hC hb T hI
  refine ⟨hIm.mk I, hIm.stronglyMeasurable_mk, MemLp.ae_eq hIm.ae_eq_mk (Lp.memLp I), ?_, ?_, ?_⟩
  · exact (integral_congr_ae hIm.ae_eq_mk).symm.trans hIzero
  · rw [← hiso]
    apply integral_congr_ae
    filter_upwards [hIm.ae_eq_mk] with ω hω
    rw [hω]
  · apply (integral_sq_error_tendsto_of_Lp_tendsto hB hm H hH hH2 T hI).congr'
    apply Filter.Eventually.of_forall
    intro n
    apply integral_congr_ae
    filter_upwards [hIm.ae_eq_mk] with ω hω
    rw [hω]

end Problem367.BrownianGrid

end

end OAI
