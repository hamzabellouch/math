import Mathlib

namespace OAI

universe uAlpha uIndex

/-! Measure identities for the five-component splitting construction. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356
namespace Splitting

variable {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]

/-- A measure supported almost everywhere on `B` vanishes on any set disjoint from `B`. -/
theorem measure_eq_zero_of_disjoint
    (ν : Measure α) {B S : Set α}
    (hν : ∀ᵐ x ∂ν, x ∈ B) (hBS : Disjoint B S) : ν S = 0 := by
  apply measure_mono_null (t := Bᶜ)
  · intro x hx
    exact fun hxB => Set.disjoint_left.mp hBS hxB hx
  · exact ae_iff.mp hν

/-- A branch pushforward vanishes away from the image of the central component. -/
theorem map_eq_zero_of_disjoint
    (ν : Measure α) {B S : Set α} {H : α → α}
    (hν : ∀ᵐ x ∂ν, x ∈ B) (hH : Measurable H)
    (hS : MeasurableSet S) (hBS : Disjoint (H '' B) S) :
    (Measure.map H ν) S = 0 := by
  rw [Measure.map_apply hH hS]
  apply measure_eq_zero_of_disjoint ν hν
  exact Set.disjoint_left.mpr fun x hxB hxS =>
    Set.disjoint_left.mp hBS ⟨x, hxB, rfl⟩ hxS

/-- An injective branch has the original mass on the image of each central subset. -/
theorem map_image_eq
    (ν : Measure α) {B S : Set α} {H : α → α}
    (hν : ∀ᵐ x ∂ν, x ∈ B) (hH : Measurable H)
    (hInj : Set.InjOn H B) (hSB : S ⊆ B)
    (hImage : MeasurableSet (H '' S)) :
    (Measure.map H ν) (H '' S) = ν S := by
  rw [Measure.map_apply hH hImage]
  apply measure_congr
  filter_upwards [hν] with x hx
  apply propext
  change H x ∈ H '' S ↔ x ∈ S
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = x := hInj (hSB hy) hx hxy
    simpa only [hyx] using hy
  · intro hxS
    exact ⟨x, hxS, rfl⟩

variable [Fintype ι]

/-- The central measure together with finitely many weighted branch pushforwards. -/
def splitMeasure (ν : Measure α) (a : ℝ≥0∞) (b : ι → ℝ≥0∞)
    (H : ι → α → α) : Measure α :=
  a • ν + ∑ i, b i • Measure.map (H i) ν

/-- Weights adding to one produce a probability measure. -/
theorem splitMeasure_isProbabilityMeasure
    (ν : Measure α) [IsProbabilityMeasure ν]
    (a : ℝ≥0∞) (b : ι → ℝ≥0∞) (H : ι → α → α)
    (hH : ∀ i, Measurable (H i)) (hweight : a + ∑ i, b i = 1) :
    IsProbabilityMeasure (splitMeasure ν a b H) := by
  have hmass : ∀ i, (Measure.map (H i) ν) Set.univ = 1 := by
    intro i
    rw [Measure.map_apply (hH i) MeasurableSet.univ]
    simp
  constructor
  simpa [splitMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.finsetSum_apply, hmass] using hweight

/-- A nonzero central coefficient transfers all almost-everywhere properties
of the mixture to its central reference measure. -/
theorem absolutelyContinuous_splitMeasure
    (ν : Measure α) (a : ℝ≥0∞) (b : ι → ℝ≥0∞) (H : ι → α → α)
    (ha : a ≠ 0) : ν ≪ splitMeasure ν a b H := by
  exact (Measure.absolutelyContinuous_smul ha).add_right _

/-- On the central component, only the central summand contributes. -/
theorem splitMeasure_apply_central
    (ν : Measure α) (a : ℝ≥0∞) (b : ι → ℝ≥0∞) (H : ι → α → α)
    {B S : Set α} (hν : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i)) (hSB : S ⊆ B) (hS : MeasurableSet S)
    (hDisj : ∀ i, Disjoint B (H i '' B)) :
    splitMeasure ν a b H S = a * ν S := by
  have hz : ∀ i, (Measure.map (H i) ν) S = 0 := by
    intro i
    apply map_eq_zero_of_disjoint ν hν (hH i) hS
    exact (hDisj i).symm.mono_right hSB
  simp [splitMeasure, Measure.add_apply, Measure.smul_apply, Measure.finsetSum_apply, hz]

/-- On one branch image only that branch summand contributes. -/
theorem splitMeasure_apply_image
    (ν : Measure α) (a : ℝ≥0∞) (b : ι → ℝ≥0∞) (H : ι → α → α)
    {B S : Set α} (hν : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i)) (hInj : ∀ i, Set.InjOn (H i) B)
    (hSB : S ⊆ B) (hImage : ∀ i, MeasurableSet (H i '' S))
    (hCentral : ∀ i, Disjoint B (H i '' B))
    (hPair : Pairwise fun i j => Disjoint (H i '' B) (H j '' B)) (j : ι) :
    splitMeasure ν a b H (H j '' S) = b j * ν S := by
  classical
  have hsub : H j '' S ⊆ H j '' B := Set.image_mono hSB
  have hz : ν (H j '' S) = 0 :=
    measure_eq_zero_of_disjoint ν hν ((hCentral j).mono_right hsub)
  have hij : ∀ i, i ≠ j → (Measure.map (H i) ν) (H j '' S) = 0 := by
    intro i hne
    exact map_eq_zero_of_disjoint ν hν (hH i) (hImage j)
      ((hPair hne).mono_right hsub)
  have hj : (Measure.map (H j) ν) (H j '' S) = ν S :=
    map_image_eq ν hν (hH j) (hInj j) hSB (hImage j)
  simp only [splitMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.finsetSum_apply, smul_eq_mul, hz, mul_zero, zero_add]
  rw [Finset.sum_eq_single j]
  · exact congrArg (b j * ·) hj
  · intro i _ hne
    simp [hij i hne]
  · simp

end Splitting
end Problem356

end

end OAI
