import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Group.Arithmetic

namespace OAI

/-! # A single profile on the two cells of a neighboring pair -/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory

variable {N S V : Type*} [Group N] [MeasurableSpace N]
  [MeasurableSpace S]

/-- Retain the first profile on the first cell and the transported second
profile elsewhere. Compatibility makes the values agree on the overlap. -/
def glueNeighborProfile (A : Set N) (t : N) (f : N → S × S) (x : N) : S := by
  classical
  exact if x ∈ A then (f x).1 else (f (x * t⁻¹)).2

variable [MeasurableMul₂ N]

theorem measurable_glueNeighborProfile {A : Set N} (hA : MeasurableSet A)
    (t : N) {f : N → S × S} (hf : Measurable f) :
    Measurable (glueNeighborProfile A t f) := by
  classical
  exact hf.fst.ite hA (hf.snd.comp (measurable_id.mul_const t⁻¹))

omit [MeasurableSpace N] [MeasurableSpace S] [MeasurableMul₂ N] in
theorem glueNeighborProfile_pair {A : Set N} (t : N) (f : N → S × S)
    (hcompat : ∀ x ∈ A, x * t ∈ A → (f (x * t)).1 = (f x).2)
    {x : N} (hx : x ∈ A) :
    (glueNeighborProfile A t f x, glueNeighborProfile A t f (x * t)) = f x := by
  classical
  have hleft : glueNeighborProfile A t f x = (f x).1 := by
    simp [glueNeighborProfile, hx]
  have hright : glueNeighborProfile A t f (x * t) = (f x).2 := by
    by_cases hxt : x * t ∈ A
    · simpa only [glueNeighborProfile, ite_eq_left hxt] using hcompat x hx hxt
    · simp [glueNeighborProfile, hxt]
  exact Prod.ext hleft hright

omit [MeasurableSpace N] [MeasurableSpace S] [MeasurableMul₂ N] in
/-- Injective evaluation into actual profiles supplies overlap compatibility
and the correct value throughout the union of the neighboring cells. -/
theorem glueNeighborProfile_actual {A : Set N} (t : N) (f : N → S × S)
    (value : S → V) (hvalue : Function.Injective value) (actual : N → V)
    (hfirst : ∀ x ∈ A, value (f x).1 = actual x)
    (hsecond : ∀ x ∈ A, value (f x).2 = actual (x * t)) :
    (∀ x ∈ A, (glueNeighborProfile A t f x,
      glueNeighborProfile A t f (x * t)) = f x) ∧
    ∀ x ∈ A ∪ (fun y => y * t) '' A,
      value (glueNeighborProfile A t f x) = actual x := by
  classical
  refine ⟨fun x hx => glueNeighborProfile_pair t f (fun y hy hyt => ?_) hx, ?_⟩
  · exact hvalue ((hfirst (y * t) hyt).trans (hsecond y hy).symm)
  · intro x hx
    by_cases hxA : x ∈ A
    · simpa only [glueNeighborProfile, ite_eq_left hxA] using hfirst x hxA
    · rcases hx with hx | ⟨y, hy, rfl⟩
      · exact (hxA hx).elim
      · simpa [glueNeighborProfile, hxA] using hsecond y hy

omit [MeasurableMul₂ N] in
/-- Gluing preserves the original joint probability law exactly. -/
theorem map_glueNeighborProfile_pair (μ : ProbabilityMeasure N)
    {A : Set N} (t : N) (f : N → S × S)
    (hμ : ∀ᵐ x ∂(μ : Measure N), x ∈ A)
    (hcompat : ∀ x ∈ A, x * t ∈ A → (f (x * t)).1 = (f x).2) :
    ProbabilityMeasure.map μ
      (fun x => (glueNeighborProfile A t f x, glueNeighborProfile A t f (x * t))) =
      ProbabilityMeasure.map μ f := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.map_congr
  filter_upwards [hμ] with x hx
  exact glueNeighborProfile_pair t f hcompat hx

end PolycyclicRecognition

end

end OAI
