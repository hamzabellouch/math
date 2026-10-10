import OAI.Analysis.CircleDomains.Probability.DyadicPhysicalOccupation
import OAI.Analysis.CircleDomains.Modulus.PhysicalTimeLength

namespace OAI

/-! The atomless time arclength measure on the open physical-domain times. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

def physicalStageTimeLength (e : G ≃ₜ U) (y₀ : Y) (n : ℕ)
    (γ : C(PathTime, X)) : Measure PathTime :=
  ∑ i : Fin (2 ^ n), rectifiableLengthCode (physicalDyadicPath e y₀ n i γ)

theorem physicalDyadicTimeLength_split (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hfin : physicalDomainLength e y₀ γ < ∞)
    (n : ℕ) (i : Fin (2 ^ n))
    (hγ : γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)) :
    rectifiableLengthCode (physicalDyadicPath e y₀ n i γ) =
      rectifiableLengthCode (physicalDyadicPath e y₀ (n + 1) (dyadicEven n i) γ) +
      rectifiableLengthCode (physicalDyadicPath e y₀ (n + 1) (dyadicOdd n i) γ) := by
  have h₁ : γ ∈ pathsInsideOn U (dyadicLeft (n + 1) (dyadicEven n i))
      (dyadicRight (n + 1) (dyadicEven n i)) := by
    apply hγ.mono_left
    rw [dyadicCell_split n i]
    exact subset_union_left
  have h₂ : γ ∈ pathsInsideOn U (dyadicLeft (n + 1) (dyadicOdd n i))
      (dyadicRight (n + 1) (dyadicOdd n i)) := by
    apply hγ.mono_left
    rw [dyadicCell_split n i]
    exact subset_union_right
  have hw := physicalDyadicPath_rectifiable e y₀ hfin n i
  have hl := physicalDyadicPath_rectifiable e y₀ hfin (n + 1) (dyadicEven n i)
  have hr := physicalDyadicPath_rectifiable e y₀ hfin (n + 1) (dyadicOdd n i)
  rw [physicalDyadicPath_of_mem e y₀ n i γ hγ] at hw ⊢
  rw [physicalDyadicPath_of_mem e y₀ (n + 1) (dyadicEven n i) γ h₁] at hl ⊢
  rw [physicalDyadicPath_of_mem e y₀ (n + 1) (dyadicOdd n i) γ h₂] at hr ⊢
  have hab : dyadicLeft n i ≤ dyadicRight (n + 1) (dyadicEven n i) := by
    simpa only [dyadicLeft_even] using dyadicLeft_le_right (n + 1) (dyadicEven n i)
  have hbc : dyadicRight (n + 1) (dyadicEven n i) ≤ dyadicRight n i := by
    simpa only [← dyadicRight_even, dyadicRight_odd] using
      dyadicLeft_le_right (n + 1) (dyadicOdd n i)
  have h₁' : γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight (n + 1) (dyadicEven n i)) := by
    simpa only [dyadicLeft_even] using h₁
  have h₂' : γ ∈ pathsInsideOn U (dyadicRight (n + 1) (dyadicEven n i)) (dyadicRight n i) := by
    simpa only [← dyadicRight_even, dyadicRight_odd] using h₂
  have heq₁ := physicalSubpath_congr_endpoints e (dyadicLeft_le_right _ _) hab γ h₁ h₁'
    (dyadicLeft_even n i) rfl
  have heq₂ := physicalSubpath_congr_endpoints e (dyadicLeft_le_right _ _) hbc γ h₂ h₂'
    (dyadicRight_even n i).symm (dyadicRight_odd n i)
  rw [heq₁] at hl ⊢
  rw [heq₂] at hr ⊢
  exact physicalSubpath_timeLength_add e hab hbc γ hγ h₁' h₂' hw hl hr

theorem physicalDyadicTimeLength_le_children (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hfin : physicalDomainLength e y₀ γ < ∞)
    (n : ℕ) (i : Fin (2 ^ n)) :
    rectifiableLengthCode (physicalDyadicPath e y₀ n i γ) ≤
      rectifiableLengthCode (physicalDyadicPath e y₀ (n + 1) (dyadicEven n i) γ) +
      rectifiableLengthCode (physicalDyadicPath e y₀ (n + 1) (dyadicOdd n i) γ) := by
  classical
  by_cases hγ : γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · exact (physicalDyadicTimeLength_split e y₀ hfin n i hγ).le
  · simp only [physicalDyadicPath, totalPhysicalSubpath, dite_eq_right hγ,
      rectifiableLengthCode_const]
    exact bot_le

theorem monotone_physicalStageTimeLength (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hfin : physicalDomainLength e y₀ γ < ∞) :
    Monotone (fun n => physicalStageTimeLength e y₀ n γ) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [physicalStageTimeLength, physicalStageTimeLength, sum_dyadic_children]
  exact Finset.sum_le_sum fun i _ => physicalDyadicTimeLength_le_children e y₀ hfin n i


def physicalTimeLength (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) : Measure PathTime :=
  increasingMeasureLimit (fun n => physicalStageTimeLength e y₀ n γ.val)
    (monotone_physicalStageTimeLength e y₀ γ.property)

theorem physicalTimeLength_apply (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    {s : Set PathTime} (hs : MeasurableSet s) :
    physicalTimeLength e y₀ γ s = ⨆ n, physicalStageTimeLength e y₀ n γ.val s :=
  increasingMeasureLimit_apply _ _ hs

theorem physicalStageTimeLength_univ (e : G ≃ₜ U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) :
    physicalStageTimeLength e y₀ n γ.val univ = physicalStageLength e y₀ n γ.val := by
  simp only [physicalStageTimeLength, Measure.coe_finsetSum, Finset.sum_apply,
    rectifiableLengthCode_univ (physicalDyadicPath_rectifiable e y₀ γ.property n _)]
  rfl

theorem physicalTimeLength_univ (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    physicalTimeLength e y₀ γ univ = physicalDomainLength e y₀ γ.val := by
  rw [physicalTimeLength_apply _ _ _ MeasurableSet.univ]
  simp only [physicalStageTimeLength_univ]
  rfl

instance (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    IsFiniteMeasure (physicalTimeLength e y₀ γ) :=
  ⟨by rw [physicalTimeLength_univ]; exact γ.property⟩

instance (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    NullSingletonClass (physicalTimeLength e y₀ γ) := by
  constructor
  intro t
  rw [physicalTimeLength_apply _ _ _ (measurableSet_singleton t)]
  simp [physicalStageTimeLength, Measure.coe_finsetSum, Finset.sum_apply, measure_singleton]

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem measurable_physicalTimeLength (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    Measurable (physicalTimeLength e y₀) := by
  apply measurable_increasingMeasureLimit
  intro n
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [physicalStageTimeLength, Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.measurable_sum
  intro i _
  exact (Measure.measurable_coe hs).comp (measurable_rectifiableLengthCode.comp
    ((measurable_totalPhysicalSubpath e hU (dyadicLeft_le_right n i) y₀).comp
      measurable_subtype_coe))

end CircleDomainRigidity

end

end OAI
