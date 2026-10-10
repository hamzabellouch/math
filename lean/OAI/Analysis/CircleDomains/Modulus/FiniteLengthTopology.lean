import OAI.Analysis.CircleDomains.Modulus.HausdorffPayment

namespace OAI

/-! Finite Hausdorff length gives a finite-continuum bound, countability
of nontrivial components, and local connectedness. -/
open Set Function MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem finite_length_continuum_bound
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [IsFiniteMeasure (μH[1] : Measure X)] : HasFiniteLargeContinuumBound X := by
  apply finite_large_continuum_bound_of_measure (μH[1] : Measure X)
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro C _hC hc hdiam
  apply hdiam.trans
  apply diam_le_of_forall_dist_le (measureReal_nonneg (μ := (μH[1] : Measure X)))
  intro x hx y hy
  have h := dist_le_hausdorffMeasure_one_of_preconnected hc.isPreconnected hy hx
  have hr := ENNReal.toReal_mono (measure_ne_top (μH[1] : Measure X) C) h
  simpa only [ENNReal.toReal_ofReal dist_nonneg, measureReal_def] using hr

 theorem finite_length_subspace_bound
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {K : Set X} (hK : (μH[1] : Measure X) K < ∞) :
    HasFiniteLargeContinuumBound K := by
  have he : (μH[1] : Measure K) univ = (μH[1] : Measure X) K := by
    have hi : Isometry (Subtype.val : K → X) := fun _ _ => rfl
    simpa only [image_univ, Subtype.range_val] using
      (hi.hausdorffMeasure_image (Or.inl (by norm_num : (0 : ℝ) ≤ 1)) univ).symm
  let : IsFiniteMeasure (μH[1] : Measure K) := ⟨he ▸ hK⟩
  exact finite_length_continuum_bound

end CircleDomainRigidity

end

end OAI
