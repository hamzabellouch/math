import OAI.Analysis.CircleDomains.Rigidity.ExactTraceFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Measure

namespace OAI

/-! Affine changes of the two scalar coordinates preserve outer-null
trace pairs, including singular changes with one constant coordinate. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem affine_pair_image_null {S : Set (ℝ × ℝ)} (hS : volume S = 0)
    (a b c d : ℝ) :
    volume ((fun x : ℝ × ℝ => (a * x.1 + b, c * x.2 + d)) '' S) = 0 := by
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (a • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (c • ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hL : volume (L '' S) = 0 := by
    rw [Measure.addHaar_image_continuousLinearMap, hS, mul_zero]
  have he : (fun x : ℝ × ℝ => (a * x.1 + b, c * x.2 + d)) '' S =
      (fun y => y - (b, d)) ⁻¹' (L '' S) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp [L]⟩
    · rintro ⟨x, hx, he⟩
      refine ⟨x, hx, ?_⟩
      have hh := congrArg (fun z : ℝ × ℝ => z + (b, d)) he
      simp only [sub_add_cancel] at hh
      change (a * x.1 + b, c * x.2 + d) = y at hh
      exact hh
  rw [he]
  simpa only [sub_eq_add_neg, measure_preimage_add_right] using hL

 theorem affine_trace_pair_null {X : Type*} (B : Set X) (u v : X → ℝ)
    (h : volume ((fun x => (u x, v x)) '' B) = 0) (a b c d : ℝ) :
    volume ((fun x => (a * u x + b, c * v x + d)) '' B) = 0 := by
  simpa only [image_image, comp_def] using affine_pair_image_null h a b c d

end CircleDomainRigidity

end

end OAI
