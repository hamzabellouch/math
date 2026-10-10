import OAI.Probability.FreeIsing.Brownian.ArrayFiltrationIntegral
import OAI.Probability.FreeIsing.Energy.FiniteIsingCrossEnergy
import OAI.Probability.FreeIsing.Estimates.FiniteIsingInnovation
import OAI.Probability.FreeIsing.Posterior.FilteringCrossLimit
import OAI.Probability.FreeIsing.Posterior.FilteringRepresentationClosure

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace Problem367.FiniteIsingFiltering

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem continuous_covariance_energy
    (P : Measure (State d Ω)) [IsFiniteMeasure P]
    (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) :
    Continuous (fun r : ℝ => ∫ p, covariance beta D v u B r.toNNReal p ^ 2 ∂P) := by
  have h := EnergyRiemann.continuous_energy
    (fun t => (memLp_covariance P beta D v u B hmB t 2).aestronglyMeasurable)
    (Eventually.of_forall (continuous_covariance beta D v u B hcB))
    (show (0 : ℝ) ≤ 2 by norm_num)
    (Eventually.of_forall fun p t => abs_covariance_le_two beta D v u B t p)
  exact h.comp (by fun_prop)

theorem mean_energy_eq_sum_covariance_energy
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) (T : ℝ≥0) :
    (∫ p, mean beta D v B T p ^ 2 ∂μ.prod (Measure.infinitePi ν)) =
      ∑ u : D, ∫ r in (0 : ℝ)..(T : ℝ),
        ∫ p, covariance beta D v u B r.toNNReal p ^ 2 ∂μ.prod (Measure.infinitePi ν) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi ν)
  have he := (hμ.integral_finiteIsingBrownianEnergy ν hB hmB D hD v T.coe_nonneg).2.1
  change (∫ r in (0 : ℝ)..(T : ℝ), ∫ p,
    ∑ u : D, finiteIsingBrownianCovariance beta D v u B r p ^ 2 ∂P) =
      ∫ p, mean beta D v B T p ^ 2 ∂P at he
  rw [← he]
  calc
    _ = ∫ r in (0 : ℝ)..(T : ℝ), ∫ p,
        ∑ u : D, covariance beta D v u B r.toNNReal p ^ 2 ∂P := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr0 : 0 ≤ r := by
        simpa only [min_eq_left T.coe_nonneg] using hr.1
      simp only [covariance, Real.coe_toNNReal r hr0]
    _ = ∫ r in (0 : ℝ)..(T : ℝ),
        ∑ u : D, ∫ p, covariance beta D v u B r.toNNReal p ^ 2 ∂P := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact integral_finsetSum _ (fun u _ =>
        (memLp_covariance P beta D v u B hmB r.toNNReal 2).integrable_sq)
    _ = _ := intervalIntegral.integral_finsetSum (fun u _ =>
      (continuous_covariance_energy P beta D v u B hmB hcB).intervalIntegrable _ _)

private theorem representation_of_driver_laws
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) (T : ℝ≥0)
    (W : D → ℝ≥0 → State d Ω → ℝ)
    (hW : ∀ u, IsPreBrownianReal (W u) (μ.prod (Measure.infinitePi ν)))
    (hAd : ∀ u, StronglyAdapted (observationFiltration B hmB D) (W u))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun p u => W u t p - W u s p) inferInstance)
      (observationFiltration B hmB D s) (μ.prod (Measure.infinitePi ν)))
    (hcross : ∀ s t, s ≤ t → Pairwise fun u w =>
      IndepFun (fun p => W u t p - W u s p) (fun p => W w t p - W w s p)
        (μ.prod (Measure.infinitePi ν)))
    (hlimit : ∀ u, Tendsto (fun n : ℕ => ∫ p, mean beta D v B T p *
      BrownianGrid.uniformSum (W u) (covariance beta D v u B) T n p
        ∂μ.prod (Measure.infinitePi ν)) atTop
      (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), ∫ p,
        covariance beta D v u B r.toNNReal p ^ 2 ∂μ.prod (Measure.infinitePi ν)))) :
    ∃ I : D → State d Ω → ℝ,
      (∀ u, MemLp (I u) 2 (μ.prod (Measure.infinitePi ν))) ∧
      (∀ u, AEStronglyMeasurable[observationFiltration B hmB D T]
        (I u) (μ.prod (Measure.infinitePi ν))) ∧
      (∀ u, (∫ p, I u p ∂μ.prod (Measure.infinitePi ν)) = 0) ∧
      (∀ u, (∫ p, I u p ^ 2 ∂μ.prod (Measure.infinitePi ν)) =
        ∫ r in (0 : ℝ)..(T : ℝ), ∫ p,
          covariance beta D v u B r.toNNReal p ^ 2 ∂μ.prod (Measure.infinitePi ν)) ∧
      (Pairwise fun u w => ∫ p, I u p * I w p ∂μ.prod (Measure.infinitePi ν) = 0) ∧
      (∀ u, Tendsto (fun n => ∫ p,
        (BrownianGrid.uniformSum (W u) (covariance beta D v u B) T n p - I u p) ^ 2
          ∂μ.prod (Measure.infinitePi ν)) atTop (𝓝 0)) ∧
      (mean beta D v B T =ᵐ[μ.prod (Measure.infinitePi ν)] fun p => ∑ u, I u p) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi ν)
  have hK (u : D) := stronglyAdapted_covariance beta D v u B hmB
  have hK2 (u : D) (t : ℝ≥0) := memLp_covariance P beta D v u B hmB t 2
  have hi (u : D) (s t : ℝ≥0) (hst : s ≤ t) :=
    BrownianArrayFiltration.coordinate_increment_indep_past (hind s t hst) u
  obtain ⟨I, hI, _, hterm, hzero, hiso, horth, happrox⟩ :=
    BrownianArrayFiltration.exists_channel_integrals hW hAd hind hcross
      (fun u => covariance beta D v u B) hK
      (fun u => Eventually.of_forall (continuous_covariance beta D v u B hcB))
      (fun _ => 2) (fun _ => by norm_num)
      (fun u => Eventually.of_forall fun p t => abs_covariance_le_two beta D v u B t p) T
  have hM := memLp_mean P beta D v B hmB T 2
  have htest (u : D) : (∫ p, mean beta D v B T p * I u p ∂P) = ∫ p, I u p ^ 2 ∂P := by
    rw [hiso u]
    exact FilteringRepresentationClosure.integral_mul_eq_of_meanSquare_limit hM (hI u)
      (fun n => BrownianFiltrationGrid.uniformSum_memLp (hW u) (hAd u) (hi u)
        _ (hK u) (hK2 u) T n) (happrox u) (hlimit u)
  refine ⟨I, hI, hterm, hzero, hiso, horth, happrox, ?_⟩
  apply FilteringRepresentationClosure.ae_eq_fintype_sum_of_cross_energy hM I hI horth htest
  calc
    _ = ∑ u : D, ∫ r in (0 : ℝ)..(T : ℝ), ∫ p,
        covariance beta D v u B r.toNNReal p ^ 2 ∂P :=
      mean_energy_eq_sum_covariance_energy hμ ν hB hmB hcB D hD v T
    _ = _ := Finset.sum_congr rfl (fun u _ => (hiso u).symm)

theorem exists_innovation_integral_representation
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) (T : ℝ≥0) :
    ∃ I : D → State d Ω → ℝ,
      (∀ u, MemLp (I u) 2 (μ.prod (Measure.infinitePi ν))) ∧
      (∀ u, AEStronglyMeasurable[observationFiltration B hmB D T]
        (I u) (μ.prod (Measure.infinitePi ν))) ∧
      (∀ u, (∫ p, I u p ∂μ.prod (Measure.infinitePi ν)) = 0) ∧
      (∀ u, (∫ p, I u p ^ 2 ∂μ.prod (Measure.infinitePi ν)) =
        ∫ r in (0 : ℝ)..(T : ℝ), ∫ p,
          covariance beta D v u B r.toNNReal p ^ 2 ∂μ.prod (Measure.infinitePi ν)) ∧
      (Pairwise fun u w => ∫ p, I u p * I w p ∂μ.prod (Measure.infinitePi ν) = 0) ∧
      (∀ u, Tendsto (fun n => ∫ p,
        (BrownianGrid.uniformSum (innovation beta D u B) (covariance beta D v u B) T n p - I u p) ^ 2
          ∂μ.prod (Measure.infinitePi ν)) atTop (𝓝 0)) ∧
      (mean beta D v B T =ᵐ[μ.prod (Measure.infinitePi ν)] fun p => ∑ u, I u p) := by
  apply representation_of_driver_laws hμ ν hB hmB hcB D hD v T
    (fun u => innovation beta D u B)
    (fun u => (innovation_isBrownianReal hμ ν hB hmB hcB D hD u).toIsPreBrownianReal)
    (fun u => innovation_stronglyAdapted beta D u B hmB hcB)
    (innovation_increment_indep_filtration hμ ν hB hmB hcB D hD)
  · intro s t hst u w huw
    have hi := (innovation_increment_law_and_indep hμ ν hB hmB hcB D hD s t hst
      (Y := fun _ => ()) measurable_const).2.1
    exact hi.indepFun huw
  · exact fun u => tendsto_cross_uniformSum hμ ν hB hmB hcB D hD v u T

theorem tendsto_uniformSum_row_meanSquare
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ p,
      ((∑ u : D, BrownianGrid.uniformSum (innovation beta D u B)
        (covariance beta D v u B) T n p) - mean beta D v B T p) ^ 2
        ∂μ.prod (Measure.infinitePi ν)) atTop (𝓝 0) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi ν)
  obtain ⟨I, hI, _, _, _, _, happrox, heq⟩ :=
    exists_innovation_integral_representation hμ ν hB hmB hcB D hD v T
  have hS (u : D) (n : ℕ) : MemLp
      (BrownianGrid.uniformSum (innovation beta D u B) (covariance beta D v u B) T n) 2 P :=
    BrownianFiltrationGrid.uniformSum_memLp
      (innovation_isBrownianReal hμ ν hB hmB hcB D hD u).toIsPreBrownianReal
      (innovation_stronglyAdapted beta D u B hmB hcB)
      (fun s t hst => BrownianArrayFiltration.coordinate_increment_indep_past
        (innovation_increment_indep_filtration hμ ν hB hmB hcB D hD s t hst) u)
      _ (stronglyAdapted_covariance beta D v u B hmB)
      (fun t => memLp_covariance P beta D v u B hmB t 2) T n
  have hl := FilteringRepresentationClosure.tendsto_integral_sq_fintype_sum_error hI hS happrox
  apply hl.congr'
  apply Eventually.of_forall
  intro n
  apply integral_congr_ae
  filter_upwards [heq] with p hp
  rw [hp]

theorem mean_martingale
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) :
    Martingale (mean beta D v B) (observationFiltration B hmB D)
      (μ.prod (Measure.infinitePi ν)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  exact (martingale_condExp (fun p : State d Ω => signal p.1 v)
    (observationFiltration B hmB D) (μ.prod (Measure.infinitePi ν))).congr
      (stronglyAdapted_mean beta D v B hmB)
      (fun t => (mean_eq_condExp hμ ν hB hmB D hD v t).symm)

end Problem367.FiniteIsingFiltering

end

end OAI
