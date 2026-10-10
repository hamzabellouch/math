import OAI.NumberTheory.Ostmann.Arithmetic.BulkPiIntegral

namespace OAI

/-! # Freeze the nonbulk coordinates and integrate the selected bulk slots -/

namespace Ostmann
open MeasureTheory
open scoped Classical

noncomputable def bulkCoordinateInsert {σ J : Type*}
    (base : σ → ℝ) (e : J ↪ σ) (y : J → ℝ) (i : σ) : ℝ :=
  if h : ∃ j, e j = i then y h.choose else base i

theorem bulkCoordinateInsert_at {σ J : Type*}
    (base : σ → ℝ) (e : J ↪ σ) (y : J → ℝ) (j : J) :
    bulkCoordinateInsert base e y (e j) = y j := by
  have h : ∃ k, e k = e j := ⟨j, rfl⟩
  rw [bulkCoordinateInsert, dite_eq_left h]
  congr 1
  exact e.injective h.choose_spec

theorem bulkCoordinateInsert_update {σ J : Type*}
    (base : σ → ℝ) (e : J ↪ σ) (y : J → ℝ) (j : J) (a : ℝ) :
    bulkCoordinateInsert base e (Function.update y j a) =
      Function.update (bulkCoordinateInsert base e y) (e j) a := by
  funext i
  by_cases h : ∃ k, e k = i
  · obtain ⟨k, rfl⟩ := h
    rw [bulkCoordinateInsert_at]
    by_cases hkj : k = j
    · subst k
      simp
    · rw [Function.update_of_ne hkj, Function.update_of_ne (fun h => hkj (e.injective h)),
        bulkCoordinateInsert_at]
  · have hne : i ≠ e j := fun hi => h ⟨j, hi.symm⟩
    rw [Function.update_of_ne hne]
    simp only [bulkCoordinateInsert, dite_eq_right h]

noncomputable def BulkIntegrand.pullBulk {σ J : Type*} [Fintype σ] [Fintype J]
    (f : BulkIntegrand σ) (base : σ → ℝ) (e : J ↪ σ) : BulkIntegrand J where
  toFun y := f (bulkCoordinateInsert base e y)
  measurable := f.measurable.comp (Measurable.of_eval fun i => by
    by_cases h : ∃ j, e j = i
    · simpa only [bulkCoordinateInsert, dite_eq_left h] using (measurable_pi_apply h.choose :
        Measurable (fun y : J → ℝ => y h.choose))
    · simpa only [bulkCoordinateInsert, dite_eq_right h] using (measurable_const :
        Measurable (fun _ : J → ℝ => base i)))
  bounded := by
    obtain ⟨C, hC, hf⟩ := f.bounded
    exact ⟨C, hC, fun y => hf _⟩

theorem BulkIntegrand.pullBulk_average {σ J : Type*} [Fintype σ] [Fintype J]
    (f : BulkIntegrand σ) (base : σ → ℝ) (e : J ↪ σ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (j : J) :
    (f.average μ (e j)).pullBulk base e = (f.pullBulk base e).average μ j := by
  ext y
  change (∫ a, f (Function.update (bulkCoordinateInsert base e y) (e j) a) ∂μ) =
    ∫ a, f (bulkCoordinateInsert base e (Function.update y j a)) ∂μ
  simp_rw [bulkCoordinateInsert_update]

theorem BulkIntegrand.pullBulk_averages {σ J : Type*} [Fintype σ] [Fintype J]
    (f : BulkIntegrand σ) (base : σ → ℝ) (e : J ↪ σ)
    (μ : σ → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] (l : List J) :
    (f.averages μ (l.map e)).pullBulk base e =
      (f.pullBulk base e).averages (fun j => μ (e j)) l := by
  induction l with
  | nil => rfl
  | cons j l ih => simp only [List.map_cons, averages, pullBulk_average, ih]

theorem BulkIntegrand.selected_bulk_integral {σ : Type*} [Fintype σ]
    {k : ℕ} (f : BulkIntegrand σ) (base : σ → ℝ) (e : Fin k ↪ σ)
    (μ : σ → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] (y : Fin k → ℝ) :
    f.averages μ ((List.finRange k).map e) (bulkCoordinateInsert base e y) =
      ∫ z, f (bulkCoordinateInsert base e z) ∂Measure.pi (fun j => μ (e j)) := by
  have h := congrArg (fun g : BulkIntegrand (Fin k) => g y)
    (f.pullBulk_averages base e μ (List.finRange k))
  rw [BulkIntegrand.averages_finRange] at h
  exact h

end Ostmann

end OAI
