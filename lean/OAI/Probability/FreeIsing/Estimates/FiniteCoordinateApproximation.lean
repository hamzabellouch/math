import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped symmDiff ENNReal

namespace Problem367

theorem exists_finite_coordinate_event
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    {A : Set (∀ i, X i)} (hA : MeasurableSet A)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (s : Finset ι) (B : Set (∀ i : s, X i)),
      MeasurableSet B ∧ μ (cylinder s B ∆ A) < ε := by
  obtain ⟨C, hC, hCA⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := μ) isSetRing_measurableCylinders
      (show ∃ D : Set (Set (∀ i, X i)), D.Countable ∧
          D ⊆ measurableCylinders X ∧ μ (⋃₀ D)ᶜ = 0 from
        ⟨{Set.univ}, Set.countable_singleton _,
          by simpa using univ_mem_measurableCylinders X, by simp⟩)
      generateFrom_measurableCylinders.symm hA hε
  obtain ⟨s, B, hB, rfl⟩ := (mem_measurableCylinders C).mp hC
  exact ⟨s, B, hB, hCA⟩

theorem exists_finite_coordinate_bool
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    {f : (∀ i, X i) → Bool} (hf : Measurable f)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (s : Finset ι) (g : (∀ i : s, X i) → Bool),
      Measurable g ∧ μ {x | g (s.restrict x) ≠ f x} < ε := by
  classical
  obtain ⟨s, B, hB, hBA⟩ := exists_finite_coordinate_event μ
    (hf (measurableSet_singleton true)) hε
  let g : (∀ i : s, X i) → Bool := fun x => if x ∈ B then true else false
  refine ⟨s, g, Measurable.ite hB measurable_const measurable_const, ?_⟩
  have hset : {x | g (s.restrict x) ≠ f x} =
      cylinder s B ∆ (f ⁻¹' {true}) := by
    ext x
    cases hfx : f x <;> by_cases hx : s.restrict x ∈ B <;>
      simp [g, Set.mem_symmDiff, cylinder, hfx, hx]
  rwa [hset]

theorem exists_finite_coordinate_indicator_L2
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    {A : Set (∀ i, X i)} (hA : MeasurableSet A)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (s : Finset ι) (B : Set (∀ i : s, X i)),
      MeasurableSet B ∧
      eLpNorm ((cylinder s B).indicator (fun _ => (1 : ℝ)) -
        A.indicator (fun _ => (1 : ℝ))) 2 μ < ε := by
  obtain ⟨s, B, hB, hBA⟩ := exists_finite_coordinate_event μ hA (ENNReal.pow_pos hε 2)
  refine ⟨s, B, hB, ?_⟩
  rw [eLpNorm_indicator_sub_indicator _ hB.cylinder.nullMeasurableSet hA.nullMeasurableSet,
    eLpNorm_indicator_const (hB.cylinder.symmDiff hA).nullMeasurableSet
      (by norm_num) (by norm_num)]
  simp only [enorm_one, one_mul, ENNReal.toReal_ofNat]
  have h := ENNReal.rpow_lt_rpow hBA (by norm_num : (0 : ℝ) < 1 / 2)
  have hpow : (ε ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = ε := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rwa [hpow] at h

end Problem367

end

end OAI
