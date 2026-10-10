import OAI.NumberTheory.Ostmann.Arithmetic.BulkCoordinateInsertion

namespace OAI

/-! # Enumerating the actual bulk slots leaves their product law unchanged -/

namespace Ostmann
open MeasureTheory
open scoped Classical

theorem bulkCoordinateInsert_reindex {σ J K : Type*}
    (base : σ → ℝ) (e : J ↪ σ) (g : K ≃ J) (y : J → ℝ) :
    bulkCoordinateInsert base (g.toEmbedding.trans e) (y ∘ g) =
      bulkCoordinateInsert base e y := by
  funext i
  by_cases hi : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := hi
    obtain ⟨k, rfl⟩ := g.surjective j
    change bulkCoordinateInsert base (g.toEmbedding.trans e) (y ∘ g)
      ((g.toEmbedding.trans e) k) = _
    rw [bulkCoordinateInsert_at, bulkCoordinateInsert_at]
    rfl
  · have hk : ¬∃ k, (g.toEmbedding.trans e) k = i := by
      rintro ⟨k, hk⟩
      exact hi ⟨g k, hk⟩
    simp only [bulkCoordinateInsert, dite_eq_right hi, dite_eq_right hk]

/-- The finite enumeration may be chosen for the proof while the product
integral remains indexed by the original tree-and-word bulk coordinates. -/
theorem BulkIntegrand.selected_bulk_integral_enum {σ J : Type*} [Fintype σ] [Fintype J]
    {k : ℕ} (f : BulkIntegrand σ) (base : σ → ℝ) (e : J ↪ σ) (g : Fin k ≃ J)
    (μ : σ → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] (y : J → ℝ) :
    f.averages μ ((List.finRange k).map (fun j => e (g j))) (bulkCoordinateInsert base e y) =
      ∫ z, f (bulkCoordinateInsert base e z) ∂Measure.pi (fun j => μ (e j)) := by
  let eg := g.toEmbedding.trans e
  have h := f.selected_bulk_integral base eg μ (y ∘ g)
  rw [bulkCoordinateInsert_reindex] at h
  refine h.trans ?_
  have he := ((measurePreserving_piCongrLeft (fun j => μ (e j)) g).symm).integral_comp'
    (fun z => f (bulkCoordinateInsert base eg z))
  refine he.symm.trans ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change f (bulkCoordinateInsert base eg (z ∘ g)) = f (bulkCoordinateInsert base e z)
    exact congrArg f (bulkCoordinateInsert_reindex base e g z)

end Ostmann

end OAI
