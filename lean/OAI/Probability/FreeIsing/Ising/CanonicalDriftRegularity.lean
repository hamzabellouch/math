import OAI.Probability.FreeIsing.Ising.CanonicalArtanh

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy

theorem norm_canonicalResponseDrift_le {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) (t : ℝ≥0) (x : Paths d) :
    ‖canonicalResponseDrift beta v t x‖ ≤
      infiniteGibbsResponseRow beta v (fun i => x i t) := by
  have hnonneg : 0 ≤ infiniteGibbsResponseRow beta v (fun i => x i t) :=
    tsum_nonneg (fun _ => sq_nonneg _)
  rw [canonicalResponseDrift, norm_mul, Real.norm_of_nonneg hnonneg]
  exact mul_le_of_le_one_left hnonneg (posterior_norm_le_one beta v t x)

theorem measurable_canonicalResponseDrift_real {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) :
    Measurable (fun p : ℝ × Paths d => canonicalResponseDrift beta v p.1.toNNReal p.2) := by
  have hc : Measurable (fun p : ℝ≥0 × Paths d => canonicalResponseDrift beta v p.1 p.2) :=
    (stronglyMeasurable_joint_of_isStronglyProgressive
      (canonicalResponseDrift_progressive beta v)).measurable
  have hn : Measurable (fun p : ℝ × Paths d => (p.1.toNNReal, p.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  exact Measurable.comp
    (g := fun p : ℝ≥0 × Paths d => canonicalResponseDrift beta v p.1 p.2)
    (f := fun p : ℝ × Paths d => (p.1.toNNReal, p.2)) hc hn

theorem canonicalResponseDrift_integrable
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Paths d => canonicalResponseDrift beta v p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)) := by
  have hi : Integrable (fun p : ℝ × Paths d =>
      infiniteGibbsResponseRow beta v (fun i => p.2 i p.1.toNNReal))
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (observationLaw μ)) := by
    simpa only [infiniteGibbsResponseRow, responseRow] using
      (observation_row_energy_integrable hμ hb v T.coe_nonneg).2.1
  exact hi.mono' (measurable_canonicalResponseDrift_real beta v).aestronglyMeasurable
    (Eventually.of_forall (fun p => norm_canonicalResponseDrift_le beta v p.1.toNNReal p.2))

theorem canonicalResponseDrift_primitive_continuous
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) :
    ∀ᵐ x ∂observationLaw μ,
      Continuous (fun t => nnrealTimePrimitive (canonicalResponseDrift beta v) t x) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply ae_continuous_nnrealTimePrimitive_of_joint
  intro n
  simpa only [NNReal.coe_natCast] using
    canonicalResponseDrift_integrable hμ hb v (n : ℝ≥0)

theorem canonicalResponseDrift_primitive_integrable
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (T : ℝ≥0) :
    Integrable (nnrealTimePrimitive (canonicalResponseDrift beta v) T)
      (observationLaw μ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  exact nnrealTimePrimitive_integrable (canonicalResponseDrift_integrable hμ hb v T)

theorem copy_canonicalResponseDrift_primitive_continuous
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (j : Bool) :
    ∀ᵐ q ∂copies beta μ, Continuous (fun t =>
      nnrealTimePrimitive (canonicalResponseDrift beta v) t (projection j q)) := by
  exact (copyProjection_measurePreserving beta μ j).quasiMeasurePreserving.ae
    (canonicalResponseDrift_primitive_continuous hμ hb v)

end Problem367.IsingObservationFactor

end

end OAI
