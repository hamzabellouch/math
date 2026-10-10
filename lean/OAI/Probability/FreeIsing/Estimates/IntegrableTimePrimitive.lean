import OAI.Probability.FreeIsing.Estimates.ProgressiveTimePrimitive

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
  {a : ℝ≥0 → Ω → ℝ}

theorem ae_intervalIntegrable_horizons_of_joint
    (ha : ∀ n : ℕ, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (n : ℝ))).prod μ)) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ,
      IntervalIntegrable (fun r : ℝ => a r.toNNReal ω) volume 0 (n : ℝ) := by
  apply ae_all_iff.mpr
  intro n
  filter_upwards [(ha n).prod_left_ae] with ω hω
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mpr hω

theorem ae_continuous_nnrealTimePrimitive_of_joint
    (ha : ∀ n : ℕ, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (n : ℝ))).prod μ)) :
    ∀ᵐ ω ∂μ, Continuous (fun t => nnrealTimePrimitive a t ω) := by
  filter_upwards [ae_intervalIntegrable_horizons_of_joint ha] with ω hω
  exact continuous_nnreal_primitive_of_integrable_horizons _ hω

omit [MeasurableSpace Ω] in
theorem nnrealTimePrimitive_nonneg {ω : Ω}
    (ha : ∀ t, 0 ≤ a t ω) (t : ℝ≥0) : 0 ≤ nnrealTimePrimitive a t ω :=
  intervalIntegral.integral_nonneg_of_forall t.coe_nonneg (fun r => ha r.toNNReal)

theorem ae_monotone_nnrealTimePrimitive_of_joint
    (ha : ∀ n : ℕ, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (n : ℝ))).prod μ))
    (hnonneg : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ a t ω) :
    ∀ᵐ ω ∂μ, Monotone (fun t => nnrealTimePrimitive a t ω) := by
  filter_upwards [ae_intervalIntegrable_horizons_of_joint ha, hnonneg] with ω hi hp
  intro s t hst
  obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
  have hit : IntervalIntegrable (fun r : ℝ => a r.toNNReal ω) volume 0 (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mpr
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mp (hi n)).mono_set
        (Ioc_subset_Ioc le_rfl hn))
  exact intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg hst
    (Filter.Eventually.of_forall (fun r => hp r.toNNReal)) hit

end Problem367

end

end OAI
