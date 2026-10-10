import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarGlobal
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneTailBounds

namespace OAI

/-! Comparison against an explicit nonnegative supersolution on the plane. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem PlaneScalarSolution.le_supersolution {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w v d : ℝ → Plane → ℝ} (hw : PlaneScalarSolution T ν a h w)
    (hT : 0 ≤ T) (hν : 0 ≤ ν) (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hcompact : CompactPlaneCoefficients a h)
    (hc : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (hs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (v t))
    (hd : ∀ t ∈ Ioc 0 T, ∀ x,
      HasDerivWithinAt (fun s => v s x) (d t x) (Icc 0 T) t)
    (he : ∀ t ∈ Ioc 0 T, ∀ x, scalarGenerator ν (a t) (v t) x + h t x ≤ d t x)
    (hv : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ v t x) :
    ∀ t ∈ Icc 0 T, ∀ x, w t x ≤ v t x := by
  obtain ⟨A, hA, hAb⟩ := hcompact.drift_bound ha T hT
  obtain ⟨B, hB⟩ := hw.bounded
  have hm := scalar_maximum_principle_bounded
    (w := fun t x => w t x - v t x)
    (d := fun t x => scalarGenerator ν (a t) (w t) x + h t x - d t x)
    (B := B)
    hT hν hA hAb
    (fun t ht x => by linarith [(le_abs_self (w t x)).trans (hB t ht x).1, hv t ht x])
    (hw.smooth.continuousOn.sub hc)
    (fun t ht => (hw.slice_smooth ht).sub (hs t ht))
    (fun t ht x => (hw.equation t ⟨ht.1.le, ht.2⟩ x).sub (hd t ht x))
    (fun t ht x => by
      rw [scalarGenerator_sub (hw.slice_smooth ⟨ht.1.le, ht.2⟩)
        (hs t ⟨ht.1.le, ht.2⟩)]
      linarith [he t ht x])
    (fun x => by rw [hw.initial]; simpa using hv 0 ⟨le_rfl, hT⟩ x)
  exact fun t ht x => sub_nonpos.mp (hm t ht x)

theorem CompactPlaneCoefficients.source_tail_bound {a : ℝ → Plane → Plane}
    {h : ℝ → Plane → ℝ} (hc : CompactPlaneCoefficients a h)
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ x,
      h t x ≤ C * planeTailProfile x := by
  obtain ⟨K, hK, hzero⟩ := hc T hT
  have hc' : Continuous (fun y : ℝ × Plane => h y.1 y.2 * planeBarrierSquare y.2 ^ 2) :=
    hh.continuous.mul ((planeBarrierSquare_smooth.continuous.comp continuous_snd).pow 2)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).bddAbove_image hc'.continuousOn
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro t ht x
  by_cases hx : x ∈ K
  · have hb : h t x * planeBarrierSquare x ^ 2 ≤ max 0 B :=
      (hB ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_right _ _)
    have hm := mul_le_mul_of_nonneg_right hb (planeTailProfile_pos x).le
    have he : planeBarrierSquare x ^ 2 * planeTailProfile x = 1 := by
      unfold planeTailProfile
      field_simp [(planeBarrierSquare_pos x).ne']
    calc
      h t x = (h t x * planeBarrierSquare x ^ 2) * planeTailProfile x := by rw [mul_assoc, he, mul_one]
      _ ≤ _ := hm
  · rw [(hzero t ht x hx).2]
    exact mul_nonneg (le_max_left _ _) (planeTailProfile_pos x).le

end ForcedComputation.VelocityDetector

end

end OAI
