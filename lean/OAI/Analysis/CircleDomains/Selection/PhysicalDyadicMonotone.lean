import OAI.Analysis.CircleDomains.Modulus.PhysicalDyadicLength
import OAI.Analysis.CircleDomains.Probability.PhysicalOccupationAdd

namespace OAI

/-! Refinement of the dyadic physical occupation measures. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

theorem rectifiableOccupationCode_const (y : Y) :
    rectifiableOccupationCode (ContinuousMap.const PathTime y) = 0 := by
  have hv : eVariationOn (ContinuousMap.const PathTime y) univ = 0 := by
    apply (eVariationOn.eq_zero_iff _).mpr
    intro _ _ _ _
    exact edist_self y
  have hb : BoundedVariationOn (ContinuousMap.const PathTime y) univ := by
    change eVariationOn (ContinuousMap.const PathTime y) univ ≠ ∞
    rw [hv]
    exact ENNReal.zero_ne_top
  apply Measure.measure_univ_eq_zero.mp
  rw [rectifiableOccupationCode_univ hb, hv]

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem physicalDyadicPath_of_mem (e : G ≃ₜ U) (y₀ : Y) (n : ℕ) (i : Fin (2 ^ n))
    (γ : C(PathTime, X)) (hγ : γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)) :
    physicalDyadicPath e y₀ n i γ = physicalSubpath e (dyadicLeft_le_right n i) ⟨γ, hγ⟩ := by
  classical
  simp only [physicalDyadicPath, totalPhysicalSubpath, dite_eq_left hγ]

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem physicalSubpath_congr_endpoints (e : G ≃ₜ U) {a b c d : PathTime}
    (hab : a ≤ b) (hcd : c ≤ d) (γ : C(PathTime, X))
    (h₁ : γ ∈ pathsInsideOn U a b) (h₂ : γ ∈ pathsInsideOn U c d)
    (ha : a = c) (hb : b = d) :
    physicalSubpath e hab ⟨γ, h₁⟩ = physicalSubpath e hcd ⟨γ, h₂⟩ := by
  cases ha
  cases hb
  rfl

theorem physicalDyadicOccupation_split (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hfin : physicalDomainLength e y₀ γ < ∞)
    (n : ℕ) (i : Fin (2 ^ n))
    (hγ : γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)) :
    rectifiableOccupationCode (physicalDyadicPath e y₀ n i γ) =
      rectifiableOccupationCode (physicalDyadicPath e y₀ (n + 1) (dyadicEven n i) γ) +
      rectifiableOccupationCode (physicalDyadicPath e y₀ (n + 1) (dyadicOdd n i) γ) := by
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
  exact physicalSubpath_occupation_add e hab hbc γ hγ h₁' h₂' hw hl hr

theorem physicalDyadicOccupation_le_children (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hfin : physicalDomainLength e y₀ γ < ∞)
    (n : ℕ) (i : Fin (2 ^ n)) :
    rectifiableOccupationCode (physicalDyadicPath e y₀ n i γ) ≤
      rectifiableOccupationCode (physicalDyadicPath e y₀ (n + 1) (dyadicEven n i) γ) +
      rectifiableOccupationCode (physicalDyadicPath e y₀ (n + 1) (dyadicOdd n i) γ) := by
  classical
  by_cases hγ : γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · exact (physicalDyadicOccupation_split e y₀ hfin n i hγ).le
  · simp only [physicalDyadicPath, totalPhysicalSubpath, dite_eq_right hγ,
      rectifiableOccupationCode_const]
    exact bot_le

theorem monotone_physicalStageOccupation (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hfin : physicalDomainLength e y₀ γ < ∞) :
    Monotone (fun n => physicalStageOccupation e y₀ n γ) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [physicalStageOccupation, physicalStageOccupation, sum_dyadic_children]
  exact Finset.sum_le_sum fun i _ => physicalDyadicOccupation_le_children e y₀ hfin n i

end CircleDomainRigidity

end

end OAI
