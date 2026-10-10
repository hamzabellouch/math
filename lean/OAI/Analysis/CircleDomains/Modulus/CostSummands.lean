import OAI.Analysis.CircleDomains.Modulus.PathCostReference

namespace OAI

/-! The three disjoint cost summands can be recovered from the total
measure. In particular a total barycenter density gives the physical
occupation density on the original domain. -/

open Set MeasureTheory Topology
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Y D : Type*} [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D]

omit [MeasurableSpace D] [BorelSpace D] in
theorem measurableEmbedding_costPhysical :
    MeasurableEmbedding (costPhysical (Y := Y) (D := D)) := by
  have hi : IsOpenEmbedding (costPhysical (Y := Y) (D := D)) := IsOpenEmbedding.inl
  exact IsOpenEmbedding.measurableEmbedding (α := Y) (β := PathCostSpace Y D) hi

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem measurableEmbedding_costAtomic :
    MeasurableEmbedding (costAtomic (Y := Y) (D := D)) := by
  have hi : IsOpenEmbedding (costAtomic (Y := Y) (D := D)) :=
    IsOpenEmbedding.inr.comp IsOpenEmbedding.inl
  exact IsOpenEmbedding.measurableEmbedding (α := D) (β := PathCostSpace Y D) hi

omit [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D] in
theorem measurableEmbedding_costTuple :
    MeasurableEmbedding (costTuple (Y := Y) (D := D)) := by
  have hi : IsOpenEmbedding (costTuple (Y := Y) (D := D)) :=
    IsOpenEmbedding.inr.comp IsOpenEmbedding.inr
  exact IsOpenEmbedding.measurableEmbedding (α := LevelTuple) (β := PathCostSpace Y D) hi

def sumCostMeasures (μ : Measure Y) (a : Measure D) (τ : Measure LevelTuple) :
    Measure (PathCostSpace Y D) :=
  μ.map costPhysical + a.map costAtomic + τ.map costTuple

theorem lintegral_sumCostMeasures (μ : Measure Y) (a : Measure D) (τ : Measure LevelTuple)
    (f : PathCostSpace Y D → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂sumCostMeasures μ a τ =
      (∫⁻ y, f (costPhysical y) ∂μ) +
      (∫⁻ s, f (costAtomic s) ∂a) + ∫⁻ t, f (costTuple t) ∂τ := by
  rw [sumCostMeasures, lintegral_add_measure, lintegral_add_measure,
    lintegral_map hf measurable_costPhysical, lintegral_map hf measurable_costAtomic,
    lintegral_map hf measurable_costTuple]

theorem sumCostMeasures_physical (μ : Measure Y) (a : Measure D) (τ : Measure LevelTuple)
    {A : Set Y} (hA : MeasurableSet A) :
    sumCostMeasures μ a τ (costPhysical '' A) = μ A := by
  have hI := (measurableEmbedding_costPhysical (Y := Y) (D := D)).measurableSet_image.mpr hA
  rw [sumCostMeasures, Measure.add_apply, Measure.add_apply,
    Measure.map_apply measurable_costPhysical hI, Measure.map_apply measurable_costAtomic hI,
    Measure.map_apply measurable_costTuple hI]
  have hself : costPhysical ⁻¹' (costPhysical (Y := Y) (D := D) '' A) = A :=
    Set.preimage_image_eq A (measurableEmbedding_costPhysical (Y := Y) (D := D)).injective
  have hatom : costAtomic ⁻¹' (costPhysical (Y := Y) (D := D) '' A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s
    rintro ⟨y, _, he⟩
    change Sum.inl y = Sum.inr (Sum.inl s) at he
    cases he
  have htuple : costTuple ⁻¹' (costPhysical (Y := Y) (D := D) '' A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t
    rintro ⟨y, _, he⟩
    change Sum.inl y = Sum.inr (Sum.inr t) at he
    cases he
  simp only [hself, hatom, htuple, measure_empty, add_zero]

theorem sumCostMeasures_atomic (μ : Measure Y) (a : Measure D) (τ : Measure LevelTuple)
    {A : Set D} (hA : MeasurableSet A) :
    sumCostMeasures μ a τ (costAtomic '' A) = a A := by
  have hI := (measurableEmbedding_costAtomic (Y := Y) (D := D)).measurableSet_image.mpr hA
  rw [sumCostMeasures, Measure.add_apply, Measure.add_apply,
    Measure.map_apply measurable_costPhysical hI, Measure.map_apply measurable_costAtomic hI,
    Measure.map_apply measurable_costTuple hI]
  have hself : costAtomic ⁻¹' (costAtomic (Y := Y) (D := D) '' A) = A :=
    Set.preimage_image_eq A (measurableEmbedding_costAtomic (Y := Y) (D := D)).injective
  have hphys : costPhysical ⁻¹' (costAtomic (Y := Y) (D := D) '' A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y
    rintro ⟨s, _, he⟩
    change Sum.inr (Sum.inl s) = Sum.inl y at he
    cases he
  have htuple : costTuple ⁻¹' (costAtomic (Y := Y) (D := D) '' A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t
    rintro ⟨s, _, he⟩
    change Sum.inr (Sum.inl s) = Sum.inr (Sum.inr t) at he
    cases Sum.inr.inj he
  simp only [hself, hphys, htuple, measure_empty, zero_add, add_zero]

theorem sumCostMeasures_tuple (μ : Measure Y) (a : Measure D) (τ : Measure LevelTuple)
    {A : Set LevelTuple} (hA : MeasurableSet A) :
    sumCostMeasures μ a τ (costTuple '' A) = τ A := by
  have hI := (measurableEmbedding_costTuple (Y := Y) (D := D)).measurableSet_image.mpr hA
  rw [sumCostMeasures, Measure.add_apply, Measure.add_apply,
    Measure.map_apply measurable_costPhysical hI, Measure.map_apply measurable_costAtomic hI,
    Measure.map_apply measurable_costTuple hI]
  have hself : costTuple ⁻¹' (costTuple (Y := Y) (D := D) '' A) = A :=
    Set.preimage_image_eq A (measurableEmbedding_costTuple (Y := Y) (D := D)).injective
  have hphys : costPhysical ⁻¹' (costTuple (Y := Y) (D := D) '' A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y
    rintro ⟨t, _, he⟩
    change Sum.inr (Sum.inr t) = Sum.inl y at he
    cases he
  have hatom : costAtomic ⁻¹' (costTuple (Y := Y) (D := D) '' A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s
    rintro ⟨t, _, he⟩
    change Sum.inr (Sum.inr t) = Sum.inr (Sum.inl s) at he
    cases Sum.inr.inj he
  simp only [hself, hphys, hatom, measure_empty, zero_add]

theorem sumCostMeasures_absolutelyContinuous {μ μ' : Measure Y} {a a' : Measure D}
    {τ τ' : Measure LevelTuple}
    (h : sumCostMeasures μ a τ ≪ sumCostMeasures μ' a' τ') :
    μ ≪ μ' ∧ a ≪ a' ∧ τ ≪ τ' := by
  refine ⟨Measure.AbsolutelyContinuous.mk ?_, Measure.AbsolutelyContinuous.mk ?_,
    Measure.AbsolutelyContinuous.mk ?_⟩
  · intro A hA hz
    rw [← sumCostMeasures_physical μ a τ hA]
    exact h (by rw [sumCostMeasures_physical μ' a' τ' hA, hz])
  · intro A hA hz
    rw [← sumCostMeasures_atomic μ a τ hA]
    exact h (by rw [sumCostMeasures_atomic μ' a' τ' hA, hz])
  · intro A hA hz
    rw [← sumCostMeasures_tuple μ a τ hA]
    exact h (by rw [sumCostMeasures_tuple μ' a' τ' hA, hz])

end CircleDomainRigidity

end

end OAI
