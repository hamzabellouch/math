import OAI.Probability.FreeIsing.Estimates.ProgressivePrimitive
import OAI.Probability.FreeIsing.Gibbs.CovarianceCriticalEnergy
import OAI.Probability.FreeIsing.Martingales.TransformL2

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367

theorem martingale_integral_increment_sq_abs
    {ι Ω : Type*} [LinearOrder ι] [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {M : ι → Ω → ℝ} (hM : Martingale M F P)
    (hM2 : ∀ t, MemLp (M t) 2 P) (s t : ι) :
    (∫ ω, (M s ω - M t ω) ^ 2 ∂P) =
      |(∫ ω, M s ω ^ 2 ∂P) - ∫ ω, M t ω ^ 2 ∂P| := by
  rcases le_total t s with hts | hst
  · have he := MartingaleTransformL2.integral_sq_increment_eq hM hts (hM2 t) (hM2 s)
    rw [he, abs_of_nonneg]
    rw [← he]
    exact integral_nonneg (fun ω => sq_nonneg _)
  · have he := MartingaleTransformL2.integral_sq_increment_eq hM hst (hM2 s) (hM2 t)
    have hswap : (∫ ω, (M s ω - M t ω) ^ 2 ∂P) =
        ∫ ω, (M t ω - M s ω) ^ 2 ∂P := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun ω => by ring)
    rw [hswap, he, abs_sub_comm, abs_of_nonneg]
    rw [← he]
    exact integral_nonneg (fun ω => sq_nonneg _)

theorem martingale_tendsto_meanSquare_of_continuous_secondMoment
    {ι Ω : Type*} [LinearOrder ι] [TopologicalSpace ι] [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {M : ι → Ω → ℝ} (hM : Martingale M F P)
    (hM2 : ∀ t, MemLp (M t) 2 P)
    (hc : Continuous (fun t => ∫ ω, M t ω ^ 2 ∂P)) (t : ι) :
    Tendsto (fun s => ∫ ω, (M s ω - M t ω) ^ 2 ∂P) (𝓝 t) (𝓝 0) := by
  simp_rw [martingale_integral_increment_sq_abs hM hM2]
  let E : ι → ℝ := fun s => ∫ ω, M s ω ^ 2 ∂P
  change Continuous E at hc
  change Tendsto (fun s => |E s - E t|) (𝓝 t) (𝓝 0)
  simpa only [sub_self, abs_zero] using ((hc.tendsto t).sub_const (E t)).abs

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_secondMoment_continuous
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i ω, Continuous (fun t => B i t ω)) (v : TreeVertex d) :
    Continuous (fun t : ℝ≥0 => ∫ p, infiniteGibbsSpinMean beta v
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi ν)
  let C := fun w p => infiniteGibbsCovariance beta v w (brownianIsingObservationR B p)
  let f := fun r : ℝ => ∫ p, ∑' w, C w (r, p) ^ 2 ∂ρ
  have hi (r : ℝ) (hr : 0 ≤ r) :
      Integrable (fun p => ∑' w, C w p ^ 2) ((volume.restrict (Ioc (0 : ℝ) r)).prod ρ) :=
    (hμ.infiniteGibbsCovariance_timeEnergy ν hB hmB hcB v hr).2.2.2.1
  have hc : Continuous (fun t : ℝ≥0 => ∫ r in (0 : ℝ)..(t : ℝ), f r) := by
    apply continuous_nnreal_primitive_of_integrable_horizons
    intro n
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mpr
      (hi n (Nat.cast_nonneg n)).integral_prod_left
  apply hc.congr
  intro t
  have he := (hμ.infiniteGibbsCovariance_timeEnergy_eq hd hb hcrit ν hB hmB hcB v t.coe_nonneg).2
  rw [intervalIntegral.integral_of_le t.coe_nonneg]
  rw [integral_prod _ (hi (t : ℝ) t.coe_nonneg)] at he
  have heval (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) :
      brownianIsingObservationR B ((t : ℝ), p) =
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) := by
    funext i
    simp only [brownianIsingObservationR, Real.toNNReal_coe]
  calc
    _ = ∫ p, infiniteGibbsSpinMean beta v
        (brownianIsingObservationR B ((t : ℝ), p)) ^ 2 ∂ρ := he
    _ = _ := integral_congr_ae (Eventually.of_forall (fun p =>
      congrArg (fun y => infiniteGibbsSpinMean beta v y ^ 2) (heval p)))

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_martingale
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i ω, Continuous (fun t => B i t ω)) (v : TreeVertex d) :
    Martingale (fun (t : ℝ≥0) (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) => infiniteGibbsSpinMean beta v
      (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))
      (arrayObservationFiltration B hmB
        (fun (σ : TreeVertex d → IsingSpin) i => spinSign (σ i)) measurable_spinSign_array)
      (μ.prod (Measure.infinitePi ν)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let F := arrayObservationFiltration B hmB
    (fun (σ : TreeVertex d → IsingSpin) i => spinSign (σ i)) measurable_spinSign_array
  let M := fun (t : ℝ≥0) (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) => infiniteGibbsSpinMean beta v
    (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))
  have hprog : IsStronglyProgressive F M := by
    apply isStronglyProgressive_infiniteGibbsSpinMean
    intro i
    have hp := (arrayNaturalFiltration_stronglyAdapted
      (plantedArrayObservation B (fun (σ : TreeVertex d → IsingSpin) i => spinSign (σ i)))
      (plantedArrayObservation_measurable hmB measurable_spinSign_array) i).isStronglyProgressive_of_continuous
      (fun p => (hcB i (p.2 i)).add (continuous_subtype_val.mul continuous_const))
    have hx : (fun (t : ℝ≥0) (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
        (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) =
        plantedArrayObservation B (fun (σ : TreeVertex d → IsingSpin) j => spinSign (σ j)) i := by
      funext t p
      exact add_comm _ _
    rw [hx]
    exact hp
  have hce (t : ℝ≥0) : M t =ᵐ[μ.prod (Measure.infinitePi ν)]
      (μ.prod (Measure.infinitePi ν))[fun p => spinSign (p.1 v) | F t] := by
    have he := hμ.infiniteGibbsSpinMean_eq_brownian_past ν hB hmB t v
    simpa only [M, F, arrayObservationFiltration, arrayNaturalFiltration_eq_comap,
      plantedArrayObservation, add_comm] using he
  exact (martingale_condExp (fun (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) => spinSign (p.1 v)) F
    (μ.prod (Measure.infinitePi ν))).congr hprog.stronglyAdapted (fun t => (hce t).symm)

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_tendsto_meanSquare
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i ω, Continuous (fun t => B i t ω)) (v : TreeVertex d) (t : ℝ≥0) :
    Tendsto (fun s : ℝ≥0 => ∫ p,
      (infiniteGibbsSpinMean beta v
        (fun i => (s : ℝ) * spinSign (p.1 i) + B i s (p.2 i)) -
       infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) (𝓝 t) (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hmart := hμ.infiniteGibbsSpinMean_brownian_martingale ν hB hmB hcB v
  apply martingale_tendsto_meanSquare_of_continuous_secondMoment hmart
  · intro s
    apply MemLp.of_bound ((hmart.stronglyMeasurable s).mono
      ((arrayObservationFiltration B hmB
        (fun (σ : TreeVertex d → IsingSpin) i => spinSign (σ i))
          measurable_spinSign_array).le s)).aestronglyMeasurable 1
    exact Eventually.of_forall (fun p => infiniteGibbsSpinMean_abs_le_one beta v _)
  · exact hμ.infiniteGibbsSpinMean_brownian_secondMoment_continuous hd hb hcrit ν hB hmB hcB v

end Problem367

end

end OAI
