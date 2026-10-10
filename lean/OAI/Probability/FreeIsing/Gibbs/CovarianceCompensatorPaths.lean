import OAI.Probability.FreeIsing.Energy.FiniteIsingEnergyLimit
import OAI.Probability.FreeIsing.Estimates.ProgressivePrimitive

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367

theorem HasFreeIsingLaw.ae_gibbsCovarianceEnergy_intervalIntegrable
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), ∀ T : ℝ≥0,
      IntervalIntegrable (fun r : ℝ => ∑' w,
        infiniteGibbsCovariance beta v w (brownianIsingObservationR B (r, p)) ^ 2)
        volume 0 (T : ℝ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hi (n : ℕ) : ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      IntervalIntegrable (fun r : ℝ => ∑' w,
        infiniteGibbsCovariance beta v w (brownianIsingObservationR B (r, p)) ^ 2)
        volume 0 (n : ℝ) := by
    have h := (hμ.infiniteGibbsCovariance_timeEnergy ν hB hmB hcB v
      (Nat.cast_nonneg n)).2.2.2.1.prod_left_ae
    filter_upwards [h] with p hp
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mpr hp
  filter_upwards [ae_all_iff.mpr hi] with p hp
  intro T
  obtain ⟨n, hn⟩ := exists_nat_gt (T : ℝ)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mpr
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mp
    (hp n)).mono_set (Ioc_subset_Ioc_right hn.le)

theorem HasFreeIsingLaw.ae_gibbsCovariancePrimitive_continuous
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), Continuous (fun T : ℝ≥0 =>
      ∫ r in (0 : ℝ)..(T : ℝ), ∑' w,
        infiniteGibbsCovariance beta v w (brownianIsingObservationR B (r, p)) ^ 2) := by
  filter_upwards [hμ.ae_gibbsCovarianceEnergy_intervalIntegrable ν hB hmB hcB v] with p hp
  apply continuous_nnreal_primitive_of_integrable_horizons
  intro n
  simpa only [NNReal.coe_natCast] using hp (n : ℝ≥0)

theorem HasFreeIsingLaw.ae_gibbsCovariancePrimitive_monotone
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), Monotone (fun T : ℝ≥0 =>
      ∫ r in (0 : ℝ)..(T : ℝ), ∑' w,
        infiniteGibbsCovariance beta v w (brownianIsingObservationR B (r, p)) ^ 2) := by
  filter_upwards [hμ.ae_gibbsCovarianceEnergy_intervalIntegrable ν hB hmB hcB v] with p hp
  intro s t hst
  exact intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg
    (show (s : ℝ) ≤ (t : ℝ) from hst)
    (Eventually.of_forall (fun _ => tsum_nonneg (fun _ => sq_nonneg _))) (hp t)

theorem HasFreeIsingLaw.ae_gibbsCovariancePrimitive_absolutelyContinuous
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), ∀ T : ℝ≥0,
      AbsolutelyContinuousOnInterval (fun t : ℝ => ∫ r in (0 : ℝ)..t, ∑' w,
        infiniteGibbsCovariance beta v w (brownianIsingObservationR B (r, p)) ^ 2)
        0 (T : ℝ) := by
  filter_upwards [hμ.ae_gibbsCovarianceEnergy_intervalIntegrable ν hB hmB hcB v] with p hp
  intro T
  exact (hp T).absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc

end Problem367

end

end OAI
