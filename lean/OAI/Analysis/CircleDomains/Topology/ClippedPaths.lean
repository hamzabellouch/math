import OAI.Analysis.CircleDomains.Probability.PathOccupation

namespace OAI

/-! Constant extension of a closed path portion. Its arclength is exactly
the variation of that portion; this is used to assemble local physical lifts. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

def timeClip (a b : PathTime) : C(PathTime, PathTime) where
  toFun t := max a (min b t)
  continuous_toFun := continuous_const.max (continuous_const.min continuous_id)

theorem monotone_timeClip (a b : PathTime) : Monotone (timeClip a b) :=
  monotone_const.max (monotone_const.min monotone_id)

theorem range_timeClip {a b : PathTime} (hab : a ≤ b) : Set.range (timeClip a b) = Icc a b := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  · intro ht
    exact ⟨t, by simp [timeClip, min_eq_right ht.2, max_eq_right ht.1]⟩

variable {X : Type*} [MetricSpace X]

theorem variation_timeClip (γ : C(PathTime, X)) {a b : PathTime} (hab : a ≤ b) :
    eVariationOn (γ.comp (timeClip a b)) univ = eVariationOn γ (Icc a b) := by
  change eVariationOn (γ ∘ timeClip a b) univ = _
  rw [eVariationOn.comp_eq_of_monotoneOn γ (timeClip a b)
    ((monotone_timeClip a b).monotoneOn univ), image_univ, range_timeClip hab]

def clippedPath (γ : RectifiablePath X) {a b : PathTime} (hab : a ≤ b) : RectifiablePath X :=
  ⟨γ.val.comp (timeClip a b), by
    change eVariationOn (γ.val.comp (timeClip a b)) univ ≠ ∞
    rw [variation_timeClip γ.val hab]
    exact γ.property.mono (subset_univ _)⟩

theorem continuous_clippedPath {a b : PathTime} (hab : a ≤ b) :
    Continuous (fun γ : RectifiablePath X => clippedPath γ hab) :=
  ((ContinuousMap.continuous_precomp (timeClip a b)).comp continuous_subtype_val).subtype_mk _

theorem pathLengthMeasure_clipped_univ (γ : RectifiablePath X)
    {a b : PathTime} (hab : a ≤ b) :
    pathLengthMeasure (clippedPath γ hab) univ = pathLengthMeasure γ (Icc a b) := by
  rw [pathLengthMeasure_univ, pathLengthMeasure_Icc γ hab]
  exact variation_timeClip γ.val hab

theorem pathLengthMeasure_clipped_Ioc (γ : RectifiablePath X)
    {a b s t : PathTime} (hab : a ≤ b) (hst : s ≤ t) :
    pathLengthMeasure (clippedPath γ hab) (Ioc s t) =
      pathLengthMeasure γ (Ioc (timeClip a b s) (timeClip a b t)) := by
  rw [pathLengthMeasure_Ioc _ hst,
    pathLengthMeasure_Ioc _ (monotone_timeClip a b hst)]
  change eVariationOn (γ.val ∘ timeClip a b) (Icc s t) = _
  have h := eVariationOn.comp_inter_Icc_eq_of_monotoneOn γ.val (timeClip a b)
    ((monotone_timeClip a b).monotoneOn univ) (mem_univ s) (mem_univ t)
  rw [univ_inter, image_univ, range_timeClip hab] at h
  rw [h, inter_eq_right.mpr]
  intro u hu
  have hs : timeClip a b s ∈ Icc a b := by rw [← range_timeClip hab]; exact mem_range_self s
  have ht : timeClip a b t ∈ Icc a b := by rw [← range_timeClip hab]; exact mem_range_self t
  exact ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩

end CircleDomainRigidity

end

end OAI
