import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneMaximumPrinciple

namespace OAI

/-! Positivity and comparison from the whole-plane maximum principle. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem CompactPlaneCoefficients.drift_bound {a : ℝ → Plane → Plane}
    {h : ℝ → Plane → ℝ} (hc : CompactPlaneCoefficients a h)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (T : ℝ) (hT : 0 ≤ T) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Icc 0 T, ∀ x, ‖a t x‖ ≤ A := by
  obtain ⟨K, hK, hzero⟩ := hc T hT
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).bddAbove_image
    (ha.continuous.norm.continuousOn :
      ContinuousOn (fun y : ℝ × Plane => ‖a y.1 y.2‖) (Icc 0 T ×ˢ K))
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro t ht x
  by_cases hx : x ∈ K
  · exact (hB ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_right _ _)
  · rw [(hzero t ht x hx).1, norm_zero]
    exact le_max_left _ _

theorem CompactPlaneCoefficients.sub {a : ℝ → Plane → Plane}
    {h k : ℝ → Plane → ℝ} (hh : CompactPlaneCoefficients a h)
    (hk : CompactPlaneCoefficients a k) :
    CompactPlaneCoefficients a (fun t x => h t x - k t x) := by
  intro T hT
  obtain ⟨K, hK, hzero⟩ := hh T hT
  obtain ⟨L, hL, kzero⟩ := hk T hT
  refine ⟨K ∪ L, hK.union hL, ?_⟩
  intro t ht x hx
  have hxK : x ∉ K := fun h => hx (Or.inl h)
  have hxL : x ∉ L := fun h => hx (Or.inr h)
  exact ⟨(hzero t ht x hxK).1, by
    change h t x - k t x = 0
    rw [(hzero t ht x hxK).2, (kzero t ht x hxL).2, sub_self]⟩

theorem PlaneScalarSolution.nonnegative {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} (hw : PlaneScalarSolution T ν a h w)
    (hT : 0 ≤ T) (hν : 0 ≤ ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (hcompact : CompactPlaneCoefficients a h)
    (hh : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ h t x) :
    ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ w t x := by
  obtain ⟨A, hA, hAb⟩ := hcompact.drift_bound ha T hT
  obtain ⟨B, hB⟩ := hw.bounded
  have he := scalar_maximum_principle_bounded
    (w := fun t x => -w t x)
    (d := fun t x => -(scalarGenerator ν (a t) (w t) x + h t x))
    hT hν hA hAb
    (fun t ht x => (neg_le_abs (w t x)).trans (hB t ht x).1)
    hw.smooth.continuousOn.neg
    (fun t ht => (hw.slice_smooth ht).neg)
    (fun t ht x => (hw.equation t ⟨ht.1.le, ht.2⟩ x).neg)
    (fun t ht x => by
      rw [scalarGenerator_neg]
      linarith [hh t ⟨ht.1.le, ht.2⟩ x])
    (fun x => by rw [hw.initial]; simp)
  exact fun t ht x => neg_nonpos.mp (he t ht x)

theorem PlaneScalarSolution.sub {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h k w v : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hv : PlaneScalarSolution T ν a k v) :
    PlaneScalarSolution T ν a (fun t x => h t x - k t x)
      (fun t x => w t x - v t x) where
  smooth := hw.smooth.sub hv.smooth
  initial := by funext x; rw [hw.initial, hv.initial]; simp
  equation := by
    intro t ht x
    convert (hw.equation t ht x).sub (hv.equation t ht x) using 1
    rw [scalarGenerator_sub (hw.slice_smooth ht) (hv.slice_smooth ht)]
    ring
  bounded := by
    obtain ⟨B, hB⟩ := hw.bounded
    obtain ⟨C, hC⟩ := hv.bounded
    refine ⟨B + C, ?_⟩
    intro t ht x
    constructor
    · exact (abs_sub _ _).trans (add_le_add (hB t ht x).1 (hC t ht x).1)
    · rw [fderiv_fun_sub ((hw.slice_smooth ht).differentiable (by simp) x)
        ((hv.slice_smooth ht).differentiable (by simp) x)]
      exact (norm_sub_le _ _).trans (add_le_add (hB t ht x).2 (hC t ht x).2)

theorem PlaneScalarSolution.compare {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h k w v : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hv : PlaneScalarSolution T ν a k v)
    (hT : 0 ≤ T) (hν : 0 ≤ ν) (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hch : CompactPlaneCoefficients a h) (hck : CompactPlaneCoefficients a k)
    (hh : ∀ t ∈ Icc 0 T, ∀ x, h t x ≤ k t x) :
    ∀ t ∈ Icc 0 T, ∀ x, w t x ≤ v t x := by
  have hp := (hv.sub hw).nonnegative hT hν ha (hck.sub hch)
    (fun t ht x => sub_nonneg.mpr (hh t ht x))
  exact fun t ht x => sub_nonneg.mp (hp t ht x)

theorem PlaneScalarSolution.unique {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w v : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hv : PlaneScalarSolution T ν a h v)
    (hT : 0 ≤ T) (hν : 0 ≤ ν) (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hc : CompactPlaneCoefficients a h) : ∀ t ∈ Icc 0 T, w t = v t := by
  intro t ht
  funext x
  exact le_antisymm
    (hw.compare hv hT hν ha hc hc (fun _ _ _ => le_rfl) t ht x)
    (hv.compare hw hT hν ha hc hc (fun _ _ _ => le_rfl) t ht x)

end ForcedComputation.VelocityDetector

end

end OAI
