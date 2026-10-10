import OAI.Analysis.CircleDomains.Selection.PhysicalDyadicMonotone
import OAI.Analysis.CircleDomains.Probability.IncreasingMeasureLimit

namespace OAI

/-! The Borel limit of the increasing dyadic physical occupation measures.
Its mass is the dyadic domain-length functional, and it is supported in the
physical domain. `PhysicalLengthCharacterization` identifies the associated
time measure with compact-interval arclength and componentwise exhaustion. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

abbrev FinitePhysicalPath (e : G ≃ₜ U) (y₀ : Y) :=
  {γ : C(PathTime, X) // physicalDomainLength e y₀ γ < ∞}

def dyadicPhysicalOccupation (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) : Measure Y :=
  increasingMeasureLimit (fun n => physicalStageOccupation e y₀ n γ.val)
    (monotone_physicalStageOccupation e y₀ γ.property)

theorem dyadicPhysicalOccupation_apply (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    {s : Set Y} (hs : MeasurableSet s) :
    dyadicPhysicalOccupation e y₀ γ s = ⨆ n, physicalStageOccupation e y₀ n γ.val s :=
  increasingMeasureLimit_apply _ _ hs

theorem dyadicPhysicalOccupation_univ (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    dyadicPhysicalOccupation e y₀ γ univ = physicalDomainLength e y₀ γ.val := by
  rw [dyadicPhysicalOccupation_apply _ _ _ MeasurableSet.univ]
  simp only [physicalStageOccupation_univ e y₀ γ.property]
  rfl

instance (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    IsFiniteMeasure (dyadicPhysicalOccupation e y₀ γ) :=
  ⟨by rw [dyadicPhysicalOccupation_univ]; exact γ.property⟩

theorem physicalStageOccupation_compl (e : G ≃ₜ U) (hG : IsOpen G) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) :
    physicalStageOccupation e y₀ n γ.val Gᶜ = 0 := by
  classical
  simp only [physicalStageOccupation, Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · have hrect := physicalDyadicPath_rectifiable e y₀ γ.property n i
    rw [physicalDyadicPath_of_mem e y₀ n i γ.val hi] at hrect ⊢
    rw [rectifiableOccupationCode_eq hrect, pathOccupation,
      Measure.map_apply (physicalSubpath e (dyadicLeft_le_right n i) ⟨γ.val, hi⟩).continuous.measurable
        hG.measurableSet.compl]
    have heq : (physicalSubpath e (dyadicLeft_le_right n i) ⟨γ.val, hi⟩) ⁻¹' Gᶜ = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact ht (physicalSubpath_mem e _ _ t)
    rw [heq, measure_empty]
  · simp [physicalDyadicPath, totalPhysicalSubpath, hi, rectifiableOccupationCode_const]

theorem dyadicPhysicalOccupation_compl (e : G ≃ₜ U) (hG : IsOpen G) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) : dyadicPhysicalOccupation e y₀ γ Gᶜ = 0 := by
  rw [dyadicPhysicalOccupation_apply _ _ _ hG.measurableSet.compl]
  simp [physicalStageOccupation_compl e hG y₀ γ]

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem measurable_dyadicPhysicalOccupation (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    Measurable (dyadicPhysicalOccupation e y₀) := by
  apply measurable_increasingMeasureLimit
  intro n
  exact (measurable_physicalStageOccupation e hU y₀ n).comp measurable_subtype_coe

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem standardBorel_finitePhysicalPath [StandardBorelSpace C(PathTime, X)]
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) : StandardBorelSpace (FinitePhysicalPath e y₀) :=
  (measurableSet_finitePhysicalDomainLength e hU y₀).standardBorel

end CircleDomainRigidity

end

end OAI
