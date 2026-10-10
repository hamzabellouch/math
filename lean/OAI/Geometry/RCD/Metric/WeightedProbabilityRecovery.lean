import OAI.Geometry.RCD.Transport.WeakGeodesicPlan

namespace OAI

/-! # Bounded probability cutoffs preserve every integrable moment

The recovery weights are the existing normalized radial cutoffs. In
particular their densities are at most two and converge pointwise to one.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
theorem integral_weighted_recovery
    (ν : Measure X) (w : ℕ → X → ℝ)
    (hw : ∀ j, Measurable (w j))
    (hb : ∀ j x, 0≤w j x ∧ w j x≤2)
    (hl : ∀ x, Tendsto (fun j => w j x) atTop (𝓝 1))
    (f : X → ℝ) (hf : Integrable f ν) :
    Tendsto (fun j => ∫x,f x ∂ν.withDensity (fun x => ENNReal.ofReal (w j x)))
      atTop (𝓝 (∫x,f x ∂ν)) := by
  have he (j : ℕ) : (∫x,f x ∂ν.withDensity (fun x => ENNReal.ofReal (w j x)))=
      ∫x,w j x*f x ∂ν := by
    rw [integral_withDensity_eq_integral_toReal_smul (hw j).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (ENNReal.ofReal (w j x)).toReal*f x=w j x*f x
      rw [ENNReal.toReal_ofReal (hb j x).1]
  simp_rw [he]
  apply tendsto_integral_of_dominated_convergence (fun x => 2*‖f x‖)
  · intro j
    exact (hw j).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · exact hf.norm.const_mul 2
  · intro j
    exact Eventually.of_forall fun x => by
      rw [norm_mul,Real.norm_eq_abs (w j x),abs_of_nonneg (hb j x).1]
      exact mul_le_mul_of_nonneg_right (hb j x).2 (norm_nonneg _)
  · exact Eventually.of_forall fun x => by simpa only [one_mul] using (hl x).mul_const (f x)

theorem weighted_probability_recovery
    (ν : ProbabilityMeasure X) (p : X) :
    ∃ (νs : ℕ → ProbabilityMeasure X) (R : ℕ → ℝ) (w : ℕ → X → ℝ),
      (∀ j, (νs j : Measure X)=(ν : Measure X).withDensity (fun x => ENNReal.ofReal (w j x))) ∧
      (∀ j, Measurable (w j)) ∧ (∀ j x, 0≤w j x ∧ w j x≤2) ∧
      (∀ x, Tendsto (fun j => w j x) atTop (𝓝 1)) ∧
      (∀ j, (νs j : Measure X)≤(2 : ℝ≥0∞) • (ν : Measure X)) ∧
      (∀ j, ∀ᵐ x ∂(νs j : Measure X), dist p x≤R j) ∧
      Tendsto νs atTop (𝓝 ν) ∧
      ∀ f : X → ℝ, Integrable f (ν : Measure X) →
        Tendsto (fun j => ∫x,f x ∂(νs j : Measure X)) atTop (𝓝 (∫x,f x ∂(ν : Measure X))) := by
  obtain ⟨w,R,hw,hb,hR,hl,hi,hm⟩ := probability_cutoff_factors (ν : Measure X) p
  have hp (j : ℕ) : IsProbabilityMeasure ((ν : Measure X).withDensity (fun x => ENNReal.ofReal (w j x))) :=
    realDensity_probability (ν : Measure X) (hi j) (Eventually.of_forall fun x => (hb j x).1) (hm j)
  let νs : ℕ → ProbabilityMeasure X := fun j => ⟨_,hp j⟩
  have hint (f : X → ℝ) (hf : Integrable f (ν : Measure X)) :
      Tendsto (fun j => ∫x,f x ∂(νs j : Measure X)) atTop (𝓝 (∫x,f x ∂(ν : Measure X))) :=
    integral_weighted_recovery _ w hw hb hl f hf
  refine ⟨νs,R,w,fun _ => rfl,hw,hb,hl,?_,?_,?_,hint⟩
  · intro j
    change (ν : Measure X).withDensity _≤_
    rw [← withDensity_const]
    apply withDensity_mono
    exact Eventually.of_forall fun x => (ENNReal.ofReal_le_ofReal (hb j x).2).trans_eq (by norm_num)
  · intro j
    change ∀ᵐ x ∂(ν : Measure X).withDensity _, _
    apply (ae_withDensity_iff (hw j).ennreal_ofReal).mpr
    exact Eventually.of_forall fun x hx => hR j x (by
      intro he
      apply hx
      simp only [he,ENNReal.ofReal_zero])
  · apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    exact hint f (f.integrable (ν : Measure X))

end RegularPointCoordinates

end

end OAI
