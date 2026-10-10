import OAI.Probability.FreeIsing.Ising.CanonicalArtanhIdentification
import OAI.Probability.FreeIsing.Ising.CommonStopBounds

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem ae_all_copyResponseDriftDifference_primitive
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (v : TreeVertex d) :
    ∀ᵐ z ∂copies beta μ, ∀ t : ℝ≥0,
      nnrealTimePrimitive (copyResponseDriftDifference beta v) t z =
        nnrealTimePrimitive (canonicalResponseDrift beta v) t z.2.1 -
          nnrealTimePrimitive (canonicalResponseDrift beta v) t z.2.2 := by
  have hi := ae_intervalIntegrable_horizons_of_joint
    (μ := observationLaw μ) (a := canonicalResponseDrift beta v)
    (fun N => by simpa only [NNReal.coe_natCast] using
      canonicalResponseDrift_integrable hμ hb v (N : ℝ≥0))
  filter_upwards [(copyProjection_measurePreserving beta μ true).quasiMeasurePreserving.ae hi,
    (copyProjection_measurePreserving beta μ false).quasiMeasurePreserving.ae hi]
    with z hl hr
  intro t
  obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
  have hrestrict {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 (N : ℝ)) :
      IntervalIntegrable f volume 0 (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mpr
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg N)).mp hf).mono_set
        (Ioc_subset_Ioc le_rfl hN))
  change (∫ s in (0 : ℝ)..(t : ℝ),
    canonicalResponseDrift beta v s.toNNReal z.2.1 -
      canonicalResponseDrift beta v s.toNNReal z.2.2) = _
  exact intervalIntegral.integral_sub (hrestrict (hl N)) (hrestrict (hr N))

theorem copied_difference_decomposition
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (v : TreeVertex d)
    {Y : ℝ≥0 → Paths d → ℝ} {Z : Bool → ℝ≥0 → Joint d → ℝ}
    (hfield : ∀ᵐ x ∂observationLaw μ, ∀ t,
      continuousField beta v t x = Y t x +
        nnrealTimePrimitive (canonicalResponseDrift beta v) t x)
    (hcopy : ∀ j, ∀ᵐ z ∂copies beta μ, ∀ t,
      Y t (projection j z) = Z j t z) :
    ∀ᵐ z ∂copies beta μ, ∀ t,
      continuousDifference beta v t z = (Z true t z - Z false t z) +
        nnrealTimePrimitive (copyResponseDriftDifference beta v) t z := by
  filter_upwards [(copyProjection_measurePreserving beta μ true).quasiMeasurePreserving.ae hfield,
    (copyProjection_measurePreserving beta μ false).quasiMeasurePreserving.ae hfield,
    hcopy true, hcopy false, ae_all_copyResponseDriftDifference_primitive hμ hb v]
    with z hl hr hzl hzr hprimitive
  intro t
  simp only [projection, Bool.false_eq_true, ite_true, ite_false] at hl hr hzl hzr
  change continuousField beta v t z.2.1 - continuousField beta v t z.2.2 = _
  rw [hl t, hr t, hprimitive t]
  have hzl' := hzl t
  have hzr' := hzr t
  change Y t z.2.1 = Z true t z at hzl'
  change Y t z.2.2 = Z false t z at hzr'
  rw [hzl', hzr']
  ring

end Problem367.IsingObservationFactor

end

end OAI
