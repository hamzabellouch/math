import OAI.Probability.FreeIsing.Gibbs.CovarianceCriticalRowConvergence

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators

namespace Problem367

theorem integral_brownianIsingObservationR_eq_interval
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)))
    [SFinite P] (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (f : (TreeVertex d → ℝ) → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hf : Integrable (fun p => f (brownianIsingObservationR B p))
      ((volume.restrict (Ioc (0 : ℝ) T)).prod P)) :
    (∫ p, f (brownianIsingObservationR B p)
      ∂(volume.restrict (Ioc (0 : ℝ) T)).prod P) =
      ∫ t in (0 : ℝ)..T, ∫ p,
        f (fun i => (t.toNNReal : ℝ) * spinSign (p.1 i) +
          B i t.toNNReal (p.2 i)) ∂P := by
  rw [intervalIntegral.integral_of_le hT, integral_prod _ hf]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  unfold brownianIsingObservationR
  simp only [Real.coe_toNNReal t ht.1.le]

theorem HasFreeIsingLaw.finiteGibbsCovariance_fullTime_interval_energy_cauchy
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    let P := μ.prod (Measure.infinitePi ν)
    let H := fun n w (t : ℝ≥0) p => finiteGibbsCovariance beta v w n
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))
    (∀ n, Summable (fun w => ∫ t in (0 : ℝ)..T,
      ∫ p, H n w t.toNNReal p ^ 2 ∂P)) ∧
    (∀ n k, Summable (fun w => ∫ t in (0 : ℝ)..T,
      ∫ p, (H n w t.toNNReal p - H k w t.toNNReal p) ^ 2 ∂P)) ∧
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
      (∑' w, ∫ t in (0 : ℝ)..T,
        ∫ p, (H n w t.toNNReal p - H k w t.toNNReal p) ^ 2 ∂P) < ε := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi ν)
  let Q := (volume.restrict (Ioc (0 : ℝ) T)).prod P
  have hX := measurable_brownianIsingObservationR hmB hcB
  have hf (n : ℕ) (w : TreeVertex d) :
      MemLp (fun p => finiteGibbsCovariance beta v w n (brownianIsingObservationR B p)) 2 Q :=
    (memLp_two_iff_integrable_sq
      (((continuous_finiteGibbsCovariance beta v w n).measurable.comp hX).aestronglyMeasurable)).2
      (integrable_finiteGibbsCovariance_sq beta v w n hX)
  have heq (n k : ℕ) (w : TreeVertex d) :=
    integral_brownianIsingObservationR_eq_interval P B
      (fun z => (finiteGibbsCovariance beta v w n z -
        finiteGibbsCovariance beta v w k z) ^ 2) hT ((hf n w).sub (hf k w)).integrable_sq
  have hr := hμ.finiteGibbsCovariance_fullTime_energy_cauchy
    hd hb hcrit ν hB hmB hcB v hT
  dsimp only [P] at heq
  dsimp only at hr
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro n
    apply summable_of_ne_finset_zero (s := connectedExhaustion v n)
    intro w hw
    simp only [finiteGibbsCovariance, dite_eq_right hw,
      zero_pow (by decide : 2 ≠ 0), integral_zero, intervalIntegral.integral_zero]
  · intro n k
    simpa only [heq] using hr.1 n k
  · simpa only [heq] using hr.2

end Problem367

end

end OAI
