import OAI.Probability.SLE.Geometry.RandomBoundaryTubes

namespace OAI

/-! The finite-valued form of Rohde--Schramm, *Basic properties of SLE*,
Annals of Mathematics 161 (2005), Theorem 4.1, pp. 898--899. The theorem
extends the inverse Loewner map continuously to the closed half-plane.
Keeping its values in `ℂ` allows arbitrary deterministic stopped charts
to act on an entire fresh continuous trace, before any passage event is
selected. This is an explicit published input, not a continuation or
passage estimate. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SLEExactGauge

local instance : LocallyCompactSpace closedHalfPlane :=
  isClosed_closedHalfPlane.locallyCompactSpace
local instance finiteBoundaryComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance finiteBoundaryComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
local instance finiteBoundaryClosedPathMeasurable : MeasurableSpace C(ℝ≥0, closedHalfPlane) := borel _
local instance finiteBoundaryClosedPathBorel : BorelSpace C(ℝ≥0, closedHalfPlane) := ⟨rfl⟩

def PublishedFiniteLoewnerBoundaryExtension : Prop :=
  ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ),
    Continuous U → IsCapacityTwoWitness U γ G F →
    ∀ t : ℝ≥0, ∃ Fbar : ℂ → ℂ,
      ContinuousOn Fbar closedHalfPlane ∧
      (∀ z ∈ upperHalfPlane, Fbar z = F t z) ∧
      Fbar (U t : ℂ) = γ t

theorem PublishedFiniteLoewnerBoundaryExtension.to_onePoint
    (h : PublishedFiniteLoewnerBoundaryExtension) : PublishedLoewnerBoundaryExtension := by
  intro U γ G F hU hw t
  obtain ⟨Fb, hc, he, ht⟩ := h U γ G F hU hw t
  exact ⟨fun z => (Fb z : OnePoint ℂ), OnePoint.continuous_coe.comp_continuousOn hc,
    fun z hz => congrArg (fun w : ℂ => (w : OnePoint ℂ)) (he z hz),
    congrArg (fun w : ℂ => (w : OnePoint ℂ)) ht⟩

theorem normalized_finite_capacity_inverse_boundary_extension
    (hpublished : PublishedFiniteLoewnerBoundaryExtension)
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (t : ℝ≥0) (c : ℝ) (hc : 0 < c) :
    ∃ Fbar : C(closedHalfPlane, ℂ),
      (∀ z : closedHalfPlane, z.1 ∈ upperHalfPlane →
        Fbar z = F t ((U t : ℂ) + (c : ℂ) * z)) ∧
      Fbar ⟨0, by simp [closedHalfPlane]⟩ = γ t := by
  obtain ⟨Fb, hFb, hext, htip⟩ := hpublished U γ G F hU hw t
  let A : ℂ → ℂ := fun z => (U t : ℂ) + (c : ℂ) * z
  have hA : Continuous A := continuous_const.add (continuous_const.mul continuous_id)
  have him (z : ℂ) : (A z).im = c * z.im := by simp [A]
  have hAc : MapsTo A closedHalfPlane closedHalfPlane := by
    intro z hz
    change 0 ≤ (A z).im
    rw [him]
    exact mul_nonneg hc.le hz
  let Fbar : C(closedHalfPlane, ℂ) := ⟨fun z => Fb (A z),
    (hFb.comp hA.continuousOn hAc).domRestrict⟩
  refine ⟨Fbar, ?_, ?_⟩
  · intro z hz
    exact hext _ (by change 0 < (A z).im; rw [him]; exact mul_pos hc hz)
  · change Fb ((U t : ℂ) + (c : ℂ) * 0) = γ t
    simpa only [mul_zero, add_zero] using htip

/-- A finite boundary chart acts measurably on continuous trace paths. -/
def finiteBoundaryPath (Fbar : C(closedHalfPlane, ℂ))
    (p : C(ℝ≥0, ℂ)) : C(ℝ≥0, ℂ) := Fbar.comp (liftClosedPath p)

theorem measurable_finiteBoundaryPath (Fbar : C(closedHalfPlane, ℂ)) :
    Measurable (finiteBoundaryPath Fbar) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact Fbar.continuous.measurable.comp
    ((continuous_eval_const t).measurable.comp measurable_liftClosedPath)

theorem finiteBoundaryPath_apply (Fbar : C(closedHalfPlane, ℂ))
    (p : C(ℝ≥0, ℂ)) (hp : ClosedPathProperty p) (t : ℝ≥0) :
    finiteBoundaryPath Fbar p t = Fbar ⟨p t, hp t⟩ := by
  change Fbar (liftClosedPath p t) = _
  congr 1
  exact Subtype.ext (liftClosedPath_apply p hp t)

end SLEExactGauge

end

end OAI
