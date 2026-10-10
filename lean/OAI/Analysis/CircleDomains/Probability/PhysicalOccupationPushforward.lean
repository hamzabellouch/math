import OAI.Analysis.CircleDomains.Selection.PhysicalTimeSupport
import OAI.Analysis.CircleDomains.Modulus.PhysicalLengthRestriction

namespace OAI

/-! Physical occupation is the pushforward of domain-time arclength, with
parameter multiplicity retained. The value assigned at dust times is irrelevant. -/

open Set MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

def physicalValue (e : G ≃ₜ U) (y₀ : Y) (x : X) : Y :=
  if h : x ∈ U then (e.symm ⟨x, h⟩).val else y₀

theorem physicalValue_subpath (e : G ≃ₜ U) (y₀ : Y)
    {a b : PathTime} (hab : a ≤ b) (γ : pathsInsideOn U a b)
    {t : PathTime} (ht : t ∈ Icc a b) :
    physicalValue e y₀ (γ.val t) = physicalSubpath e hab γ t := by
  simp only [physicalValue, dite_eq_left (γ.property ht), physicalSubpath,
    ContinuousMap.coe_mk, timeClip, min_eq_right ht.2, max_eq_right ht.1]

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

theorem measurable_physicalValue (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    Measurable (physicalValue e y₀) :=
  (continuous_subtype_val.comp e.symm.continuous).measurable.dite
    measurable_const hU.measurableSet

omit [MeasurableSpace X] [BorelSpace X] in
theorem physicalDyadicLength_map (e : G ≃ₜ U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) (i : Fin (2 ^ n)) :
    (rectifiableLengthCode (physicalDyadicPath e y₀ n i γ.val)).map
        (physicalValue e y₀ ∘ γ.val) =
      rectifiableOccupationCode (physicalDyadicPath e y₀ n i γ.val) := by
  by_cases hi : γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · have hr := physicalDyadicPath_rectifiable e y₀ γ.property n i
    rw [physicalDyadicPath_of_mem e y₀ n i γ.val hi] at hr ⊢
    rw [rectifiableLengthCode_eq hr, rectifiableOccupationCode_eq hr, pathOccupation]
    apply Measure.map_congr
    have hae : ∀ᵐ t ∂pathLengthMeasure
        ⟨physicalSubpath e (dyadicLeft_le_right n i) ⟨γ.val, hi⟩, hr⟩,
        t ∈ Icc (dyadicLeft n i) (dyadicRight n i) := by
      have heq := physicalSubpath_timeLength_portion e (dyadicLeft_le_right n i) ⟨γ.val, hi⟩ hr
      rw [rectifiableLengthCode_eq hr] at heq
      rw [heq]
      exact ae_restrict_mem measurableSet_Icc
    filter_upwards [hae] with t ht
    exact physicalValue_subpath e y₀ (dyadicLeft_le_right n i) ⟨γ.val, hi⟩ ht
  · simp [physicalDyadicPath, totalPhysicalSubpath, hi,
      rectifiableLengthCode_const, rectifiableOccupationCode_const]

theorem physicalStageTimeLength_map (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) :
    (physicalStageTimeLength e y₀ n γ.val).map (physicalValue e y₀ ∘ γ.val) =
      physicalStageOccupation e y₀ n γ.val := by
  have hm := (measurable_physicalValue e hU y₀).comp γ.val.continuous.measurable
  ext s hs
  rw [Measure.map_apply hm hs]
  simp only [physicalStageTimeLength, physicalStageOccupation, Measure.coe_finsetSum,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← physicalDyadicLength_map e y₀ γ n i, Measure.map_apply hm hs]

theorem physicalTimeLength_map (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) :
    (physicalTimeLength e y₀ γ).map (physicalValue e y₀ ∘ γ.val) =
      dyadicPhysicalOccupation e y₀ γ := by
  have hm := (measurable_physicalValue e hU y₀).comp γ.val.continuous.measurable
  ext s hs
  rw [Measure.map_apply hm hs, physicalTimeLength_apply _ _ _ (hm hs),
    dyadicPhysicalOccupation_apply _ _ _ hs]
  congr 1
  funext n
  rw [← physicalStageTimeLength_map e hU y₀ γ n, Measure.map_apply hm hs]

theorem physicalOccupation_integral (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ γ =
      ∫⁻ t, g (physicalValue e y₀ (γ.val t)) ∂physicalTimeLength e y₀ γ := by
  rw [← physicalTimeLength_map e hU y₀ γ]
  exact lintegral_map hg ((measurable_physicalValue e hU y₀).comp γ.val.continuous.measurable)

end CircleDomainRigidity

end

end OAI
