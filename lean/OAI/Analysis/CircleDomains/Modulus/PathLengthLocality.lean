import OAI.Analysis.CircleDomains.Probability.PathPortionMeasure
import OAI.Analysis.CircleDomains.Probability.RectifiableOccupationCode

namespace OAI

/-! Time arclength is local on closed intervals and adds at shared endpoints. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def rectifiableLengthCode (γ : C(PathTime, X)) : Measure PathTime :=
  if h : BoundedVariationOn γ univ then pathLengthMeasure ⟨γ, h⟩ else 0

theorem rectifiableLengthCode_eq {γ : C(PathTime, X)} (hγ : BoundedVariationOn γ univ) :
    rectifiableLengthCode γ = pathLengthMeasure ⟨γ, hγ⟩ := by
  simp only [rectifiableLengthCode, dite_eq_left hγ]

theorem rectifiableLengthCode_univ {γ : C(PathTime, X)} (hγ : BoundedVariationOn γ univ) :
    rectifiableLengthCode γ univ = eVariationOn γ univ := by
  rw [rectifiableLengthCode_eq hγ, pathLengthMeasure_univ]

instance (γ : C(PathTime, X)) : IsFiniteMeasure (rectifiableLengthCode γ) := by
  by_cases hγ : BoundedVariationOn γ univ
  · rw [rectifiableLengthCode_eq hγ]; infer_instance
  · simp only [rectifiableLengthCode, dite_eq_right hγ]; infer_instance

instance (γ : C(PathTime, X)) : NullSingletonClass (rectifiableLengthCode γ) := by
  by_cases hγ : BoundedVariationOn γ univ
  · rw [rectifiableLengthCode_eq hγ]; infer_instance
  · simp only [rectifiableLengthCode, dite_eq_right hγ]
    exact ⟨fun _ => by simp⟩

theorem rectifiableLengthCode_const (x : X) :
    rectifiableLengthCode (ContinuousMap.const PathTime x) = 0 := by
  have hv : eVariationOn (ContinuousMap.const PathTime x) univ = 0 := by
    apply (eVariationOn.eq_zero_iff _).mpr
    intro _ _ _ _
    exact edist_self x
  have hb : BoundedVariationOn (ContinuousMap.const PathTime x) univ := by
    change eVariationOn _ _ ≠ ∞
    rw [hv]
    exact ENNReal.zero_ne_top
  apply Measure.measure_univ_eq_zero.mp
  rw [rectifiableLengthCode_univ hb, hv]

theorem pathLengthMeasure_restrict_congr (γ η : RectifiablePath X) {a b : PathTime}
    (heq : EqOn γ.val η.val (Icc a b)) :
    (pathLengthMeasure γ).restrict (Icc a b) =
      (pathLengthMeasure η).restrict (Icc a b) := by
  by_cases hab : a ≤ b
  · rw [← pathLengthMeasure_clipped γ hab, ← pathLengthMeasure_clipped η hab]
    congr 1
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    apply heq
    rw [← range_timeClip hab]
    exact mem_range_self t
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hab)]
    simp

theorem pathLengthMeasure_restrict_add (γ : RectifiablePath X)
    {a b c : PathTime} (hab : a ≤ b) (hbc : b ≤ c) :
    (pathLengthMeasure γ).restrict (Icc a c) =
      (pathLengthMeasure γ).restrict (Icc a b) +
      (pathLengthMeasure γ).restrict (Icc b c) := by
  have hd : AEDisjoint (pathLengthMeasure γ) (Icc a b) (Icc b c) := by
    rw [AEDisjoint]
    have heq : Icc a b ∩ Icc b c = {b} := by
      ext t
      simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
      constructor
      · rintro ⟨⟨_, h₁⟩, h₂, _⟩
        exact h₁.antisymm h₂
      · rintro rfl
        exact ⟨⟨hab, le_rfl⟩, le_rfl, hbc⟩
    rw [heq]
    exact measure_singleton b
  rw [← Icc_union_Icc_eq_Icc hab hbc]
  exact Measure.restrict_union₀ hd measurableSet_Icc.nullMeasurableSet

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_rectifiableLengthCode : Measurable (rectifiableLengthCode (X := X)) :=
  measurable_pathLengthMeasure.dite measurable_const measurableSet_rectifiablePaths

end CircleDomainRigidity

end

end OAI
