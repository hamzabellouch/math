import Mathlib

namespace OAI

universe uAlpha uIndex

/-!
# The deterministic-selection mass obstruction

A preserving map cannot carry a positive-mass selection set into a target
whose prescribed mass is a strictly smaller multiple of the same reference
mass.  This is the measure-theoretic obstruction in the Coulomb construction.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.Splitting

variable {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]

/-- Preservation and a strict compression of the reference mass force the
selected set to have reference measure zero. -/
theorem reference_mass_zero_of_compression
    {μ ν : Measure α} {T : α → α} {S A : Set α} {c d : ℝ≥0∞}
    (hT : Measurable T) (hpres : Measure.map T μ = μ)
    (hA : MeasurableSet A) (hsub : S ⊆ T ⁻¹' A)
    (hsource : μ S = c * ν S) (htarget : μ A = d * ν S)
    (hdc : d < c) (hfinite : ν S ≠ ⊤) : ν S = 0 := by
  by_contra hne
  have hle : c * ν S ≤ d * ν S := calc
    c * ν S = μ S := hsource.symm
    _ ≤ μ (T ⁻¹' A) := measure_mono hsub
    _ = (Measure.map T μ) A := (Measure.map_apply hT hA).symm
    _ = μ A := by rw [hpres]
    _ = d * ν S := htarget
  exact (not_lt_of_ge hle)
    ((ENNReal.mul_lt_mul_iff_left hne hfinite).2 hdc)

/-- No preserving map can implement a countable almost-everywhere selection
whose source and target masses have a uniformly strict reversed ratio. -/
theorem not_preserving_of_countable_compression [Countable ι]
    {μ ν : Measure α} [IsFiniteMeasure ν]
    {T : α → α} {S A : ι → Set α} {c d : ℝ≥0∞}
    (hν : ν Set.univ ≠ 0)
    (hA : ∀ i, MeasurableSet (A i))
    (hsub : ∀ i, S i ⊆ T ⁻¹' A i)
    (hsource : ∀ i, μ (S i) = c * ν (S i))
    (htarget : ∀ i, μ (A i) = d * ν (S i))
    (hdc : d < c)
    (hcover : ∀ᵐ x ∂ν, ∃ i, x ∈ S i) :
    ¬ (Measurable T ∧ Measure.map T μ = μ) := by
  rintro ⟨hT, hpres⟩
  have hzero : ∀ i, ν (S i) = 0 := fun i =>
    reference_mass_zero_of_compression hT hpres (hA i) (hsub i)
      (hsource i) (htarget i) hdc (measure_ne_top ν (S i))
  have hnull : ν (⋃ i, S i) = 0 := measure_iUnion_null hzero
  have hfull : (⋃ i, S i) =ᵐ[ν] Set.univ := by
    filter_upwards [hcover] with x hx
    apply propext
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact hx
  exact hν ((measure_congr hfull).symm.trans hnull)

/-- The branch-selection formulation. The hypotheses about selected-set
masses are exactly those supplied by disjoint weighted pushforward
components. No regularity beyond measurability is imposed on the selector. -/
theorem no_preserving_branch_selection [Countable ι] [MeasurableEq α]
    {μ ν : Measure α} [IsFiniteMeasure ν] {B : Set α}
    {H : ι → α → α} {c d : ℝ≥0∞}
    (hν : ν Set.univ ≠ 0) (hB : MeasurableSet B)
    (hfull : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i))
    (himage : ∀ i S, MeasurableSet S → S ⊆ B →
      MeasurableSet (H i '' S))
    (hsource : ∀ S, MeasurableSet S → S ⊆ B → μ S = c * ν S)
    (htarget : ∀ i S, MeasurableSet S → S ⊆ B →
      μ (H i '' S) = d * ν S)
    (hdc : d < c) :
    ¬ ∃ T : α → α, Measurable T ∧ Measure.map T μ = μ ∧
      (∀ᵐ x ∂ν, ∃ i, T x = H i x) := by
  rintro ⟨T, hT, hpres, hselect⟩
  let S : ι → Set α := fun i => B ∩ {x | T x = H i x}
  have hS : ∀ i, MeasurableSet (S i) := fun i =>
    hB.inter (measurableSet_eq_fun hT (hH i))
  have hSB : ∀ i, S i ⊆ B := fun _ => Set.inter_subset_left
  have hsub : ∀ i, S i ⊆ T ⁻¹' (H i '' S i) := by
    intro i x hx
    exact ⟨x, hx, hx.2.symm⟩
  have hcover : ∀ᵐ x ∂ν, ∃ i, x ∈ S i := by
    filter_upwards [hfull, hselect] with x hx hsel
    obtain ⟨i, hi⟩ := hsel
    exact ⟨i, hx, hi⟩
  exact not_preserving_of_countable_compression hν
    (fun i => himage i (S i) (hS i) (hSB i)) hsub
    (fun i => hsource (S i) (hS i) (hSB i))
    (fun i => htarget i (S i) (hS i) (hSB i)) hdc hcover ⟨hT, hpres⟩

end Problem356.Splitting

end

end OAI
