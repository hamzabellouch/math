import OAI.NumberTheory.TwoPoint.Bounds.CoordinateEmbedding
import OAI.NumberTheory.TwoPoint.Walks.TupleColumnResampling

namespace OAI

/-! The ambient column rank is exactly the rank on its observed prime classes. -/

namespace TwoPointCorrelations

open scoped Classical

lemma resampledTupleColumnPattern_label_map {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) :
    Subtype.val ∘ (resampledTupleColumnPattern w hR forward padding j).label =
      (tupleColumnPattern w hR forward padding j).label := rfl

lemma resampledTupleColumnPattern_coefficient {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) (h : ℕ) :
    (resampledTupleColumnPattern w hR forward padding j).coefficient h =
      (tupleColumnPattern w hR forward padding j).coefficient h := rfl

/-- The selected rank witness is unchanged by restriction to the smaller
resampling space. -/
theorem tuple_column_observed_rank_iff {J R : ℕ} {P : Fin J → Finset ℕ}
    {ρ : Type*} (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J) (h : ℕ)
    (left right : ρ → ℕ) (control : ρ → patternClasses (w j)) :
    LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture (resampledTupleColumnPattern w hR forward padding j).label
          (fun t => ((resampledTupleColumnPattern w hR forward padding j).coefficient h t : ℝ)) (left i) -
        formalDeparture (resampledTupleColumnPattern w hR forward padding j).label
          (fun t => ((resampledTupleColumnPattern w hR forward padding j).coefficient h t : ℝ)) (right i))
      (fun i => Pi.basisFun ℝ (patternClasses (w j)) (control i))) ↔
    LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture (tupleColumnPattern w hR forward padding j).label
          (fun t => ((tupleColumnPattern w hR forward padding j).coefficient h t : ℝ)) (left i) -
        formalDeparture (tupleColumnPattern w hR forward padding j).label
          (fun t => ((tupleColumnPattern w hR forward padding j).coefficient h t : ℝ)) (right i))
      (fun i => Pi.basisFun ℝ (P j) (control i).val)) := by
  have he := selected_rank_rename_iff
    (Subtype.val : patternClasses (w j) → P j) Subtype.val_injective
    (resampledTupleColumnPattern w hR forward padding j).label
    (fun t => ((resampledTupleColumnPattern w hR forward padding j).coefficient h t : ℝ))
    left right control
  simpa only [resampledTupleColumnPattern_label_map,
    resampledTupleColumnPattern_coefficient] using he

end TwoPointCorrelations

end OAI
