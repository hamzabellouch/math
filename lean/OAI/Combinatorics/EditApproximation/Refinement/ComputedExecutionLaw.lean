import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseExecution
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The coarse sampler execution and its returned seed share one probability space. -/

namespace EditApproximation

open MeasureTheory








instance computedExecutionLaw_probability (source target : List ℕ) (N : ℕ) :
    IsProbabilityMeasure (computedExecutionLaw source target N) := by
  unfold computedExecutionLaw
  infer_instance



 theorem computedExecutionProjection_measurable (source target : List ℕ) (N : ℕ) :
    Measurable (computedExecutionProjection source target N) :=
  physicalCoarseExecutionProjection_measurable source target N (integerParameters N).P
    (inputHeight N) (integerParameters N).B (computedPhysicalCoarseDepth source target N)

 theorem computedExecutionProjection_law (source target : List ℕ) (N : ℕ) :
    (computedExecutionLaw source target N).map (computedExecutionProjection source target N) =
      physicalFamilyRuntimeLaw (R := inputHeight N ^ 2) target N (integerParameters N).P
        (inputHeight N) (physicalCoarseSeedLaw (M := (integerParameters N).M)
          (J := intervalTreeDepth (integerParameters N).M source.length) source target N (integerParameters N).B
          (computedPhysicalCoarseDepth source target N)) :=
  physicalCoarseExecutionProjection_law source target N (integerParameters N).P
    (inputHeight N) (integerParameters N).B (computedPhysicalCoarseDepth source target N)



instance computedFullOutcome_measurableSingleton (source target : List ℕ) (N : ℕ) :
    MeasurableSingletonClass (ComputedFullOutcome source target N) := by
  refine ⟨fun outcome => ?_⟩
  exact measurableSet_sum_iff.mpr
    ⟨(Set.to_countable _).measurableSet, (Set.to_countable _).measurableSet⟩



instance computedFullLaw_probability (source target : List ℕ) (N : ℕ) (epsilon : BinaryFraction) :
    IsProbabilityMeasure (computedFullLaw source target N epsilon) := by
  classical
  unfold computedFullLaw
  split <;> infer_instance

noncomputable def computedFullProjection (source target : List ℕ) (N : ℕ) :
    ComputedFullOutcome source target N → ComputedPhysicalOutcome source target N
  | .inl _ => .inl ()
  | .inr execution => .inr (computedExecutionProjection source target N execution)

 theorem computedFullProjection_measurable (source target : List ℕ) (N : ℕ) :
    Measurable (computedFullProjection source target N) := by
  apply measurable_fun_sum
  · exact measurable_const
  · exact measurable_inr.comp (computedExecutionProjection_measurable source target N)

noncomputable def computedFullAnswer (source target : List ℕ) (N : ℕ)
    (outcome : ComputedFullOutcome source target N) : ℕ :=
  computedPhysicalAnswer source target N (computedFullProjection source target N outcome)

 theorem computedFullProjection_law (source target : List ℕ) (N : ℕ) (epsilon : BinaryFraction) :
    (computedFullLaw source target N epsilon).map (computedFullProjection source target N) =
      computedPhysicalLaw source target N epsilon := by
  unfold computedFullLaw computedPhysicalLaw physicalUniformLaw
  split_ifs with hlarge
  · rw [Measure.map_map (computedFullProjection_measurable source target N) measurable_inr]
    have heq : computedFullProjection source target N ∘ Sum.inr =
        Sum.inr ∘ computedExecutionProjection source target N := rfl
    rw [heq, ← Measure.map_map measurable_inr (computedExecutionProjection_measurable source target N),
      computedExecutionProjection_law]
  · rw [Measure.map_dirac]
    rfl

 theorem computedFullAnswer_equal (source target : List ℕ) (N : ℕ) (heq : source = target)
    (outcome : ComputedFullOutcome source target N) : computedFullAnswer source target N outcome = 0 :=
  computedPhysicalAnswer_equal source target N heq _


 theorem computed_full_conditional_accuracy (source target : List ℕ) (N : ℕ)
    (epsilon : BinaryFraction) (hepsilon : 0 < epsilon.value)
    (hsize : source.length + target.length ≤ N)
    (coarseBernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin (integerParameters N).B =>
      (PMF.uniformOfFintype (Fin (integerParameters N).B)).toMeasure))
    (groupBernstein : ∀ b : ℕ, ∀ h : Fin
      (groupDyadicScales (integerParameters N).M b (inputSmallLog N)).length,
      FiniteBernsteinInput (Measure.pi fun _ : Fin
        (groupSampleCount (integerParameters N).M (inputSmallLog N ^ 80) b
          (groupDyadicScaleAt (integerParameters N).M b (inputSmallLog N) h)) =>
        (PMF.uniformOfFintype (Fin (integerParameters N).M)).toMeasure)) :
    (2 / 3 : ℝ) ≤ (computedFullLaw source target N epsilon).real
      {outcome | EditDistortion.edit source target ≤ computedFullAnswer source target N outcome ∧
        (computedFullAnswer source target N outcome : ℝ) ≤
          (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target} := by
  have h := computed_physical_uniform_conditional_accuracy source target N epsilon hepsilon hsize
    coarseBernstein groupBernstein
  rw [← computedFullProjection_law source target N epsilon,
    map_measureReal_apply (computedFullProjection_measurable source target N)
      (Set.to_countable _).measurableSet] at h
  exact h

end EditApproximation

end OAI
