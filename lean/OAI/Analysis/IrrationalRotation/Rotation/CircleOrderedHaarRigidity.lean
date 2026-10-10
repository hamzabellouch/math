import OAI.Analysis.IrrationalRotation.Analysis.OrderedHaarRigidity
import OAI.Analysis.IrrationalRotation.Sampling.CircleSamplingKernelBridge

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.CircleOrderedRigidity

theorem coordinate_bounds (p : CircleParameterData) (i : ℕ) (x : Circle) :
    0 ≤ p.coordinate i x ∧ p.coordinate i x < 1 := by
  simpa [CircleParameterData.coordinate, CircleParameterData.rep] using
    (AddCircle.equivIco (1 : ℝ) 0 (p.q i • x)).property

theorem coordinate_integrable (p : CircleParameterData) (i : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → Circle} (hf : Measurable f) :
    Integrable (fun ω => p.coordinate i (f ω)) μ := by
  apply Integrable.of_bound
    ((p.measurable_coordinate i).comp hf).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun ω => by
    change ‖p.coordinate i (f ω)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (coordinate_bounds p i (f ω)).1]
    exact (coordinate_bounds p i (f ω)).2.le

theorem ae_coordinate_eq_of_ordered_equal_marginals
    (p : CircleParameterData) (η : Measure (Circle × Circle)) [IsFiniteMeasure η]
    (hmarg : η.map Prod.fst = η.map Prod.snd)
    (horder : ∀ᵐ xy ∂η, ∀ i : ℕ, 1 ≤ i →
      p.coordinate i xy.1 ≤ p.coordinate i xy.2) :
    ∀ᵐ xy ∂η, ∀ i : ℕ, 1 ≤ i → p.coordinate i xy.1 = p.coordinate i xy.2 := by
  apply ae_all_iff.2
  intro i
  by_cases hi : 1 ≤ i
  · have heq : (fun xy : Circle × Circle => p.coordinate i xy.1) =ᵐ[η]
        fun xy => p.coordinate i xy.2 := by
      apply (integral_eq_iff_of_ae_le
        (coordinate_integrable p i measurable_fst)
        (coordinate_integrable p i measurable_snd)
        (horder.mono fun xy hxy => hxy i hi)).1
      have hg := (p.measurable_coordinate i).stronglyMeasurable
      calc
        (∫ xy, p.coordinate i xy.1 ∂η) =
            ∫ x, p.coordinate i x ∂η.map Prod.fst :=
          (integral_map_of_stronglyMeasurable measurable_fst hg).symm
        _ = ∫ x, p.coordinate i x ∂η.map Prod.snd := by rw [hmarg]
        _ = ∫ xy, p.coordinate i xy.2 ∂η :=
          integral_map_of_stronglyMeasurable measurable_snd hg
    exact heq.mono fun _ h _ => h
  · exact Filter.Eventually.of_forall fun _ h => (hi h).elim

theorem ae_coordinate_eq_of_ordered_haar_marginals
    (p : CircleParameterData) (η : Measure (Circle × Circle))
    (hfst : η.map Prod.fst = circleMeasure)
    (hsnd : η.map Prod.snd = circleMeasure)
    (horder : ∀ᵐ xy ∂η, ∀ i : ℕ, 1 ≤ i →
      p.coordinate i xy.1 ≤ p.coordinate i xy.2) :
    ∀ᵐ xy ∂η, ∀ i : ℕ, 1 ≤ i → p.coordinate i xy.1 = p.coordinate i xy.2 := by
  have : IsProbabilityMeasure (η.map Prod.fst) := hfst ▸ circleMeasure_probability
  have : IsProbabilityMeasure η :=
    Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable
  exact ae_coordinate_eq_of_ordered_equal_marginals p η (hfst.trans hsnd.symm) horder

theorem ae_no_threshold_crossings_of_ordered_haar_marginals
    (p : CircleParameterData) (η : Measure (Circle × Circle))
    (hfst : η.map Prod.fst = circleMeasure)
    (hsnd : η.map Prod.snd = circleMeasure)
    (horder : ∀ᵐ xy ∂η, ∀ i : ℕ, 1 ≤ i →
      p.coordinate i xy.1 ≤ p.coordinate i xy.2) :
    ∀ᵐ xy ∂η, ∀ i : ℕ, 1 ≤ i → ∀ u : ℝ,
      ¬ (p.coordinate i xy.1 < u ∧ u ≤ p.coordinate i xy.2) := by
  filter_upwards [ae_coordinate_eq_of_ordered_haar_marginals p η hfst hsnd horder]
    with xy hxy
  intro i hi u hcross
  exact (not_lt_of_ge (hxy i hi ▸ hcross.2)) hcross.1

end Invariant233.CircleOrderedRigidity

end

end OAI
