import OAI.NumberTheory.DukePrimeDegree.Geometry.WeylReindex
import OAI.NumberTheory.PrimePackets.RootRelations

namespace OAI

/-! # Entropy under coordinate permutations of the quotient -/

noncomputable section
open MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

theorem measureEntropy_map_measurableEquiv {Y Z : Type*}
    [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure Y) (e : Y ≃ᵐ Z) (S : Y → Y) (T : Z → Z)
    (hS : Measurable S) (hT : Measurable T)
    (h : ∀ y, e (S y) = T (e y)) :
    measureEntropy (μ.map e) T = measureEntropy μ S := by
  apply le_antisymm
  · exact measureEntropy_map_semiconj_le μ e e.measurable S T hT h
  · have hi (z : Z) : e.symm (T z) = S (e.symm z) := by
      apply e.injective
      simpa only [e.apply_symm_apply] using (h (e.symm z)).symm
    have H := measureEntropy_map_semiconj_le (μ.map e) e.symm e.symm.measurable T S hS hi
    have hmap : (μ.map e).map e.symm = μ := by
      rw [Measure.map_map e.symm.measurable e.measurable]
      have he : e.symm ∘ e = id := by funext y; exact e.symm_apply_apply y
      rw [he, Measure.map_id]
    rwa [hmap] at H

lemma permutedWeight_sum {n : ℕ} (e : Equiv.Perm (Fin n))
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) :
    ∑ i, ell (e.symm i) = 0 := by
  rw [Equiv.sum_comp]
  exact hell

lemma reindex_diagonalOneParameter {n : ℕ} (e : Equiv.Perm (Fin n))
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ) :
    reindexSpecialLinear ℝ e (diagonalOneParameter ell hell t) =
      diagonalOneParameter (fun i => ell (e.symm i)) (permutedWeight_sum e ell hell) t := by
  apply Subtype.ext
  ext i j
  change (Matrix.diagonal (fun k => Real.exp (ell k * t))) (e.symm i) (e.symm j) =
    (Matrix.diagonal (fun k => Real.exp (ell (e.symm k) * t))) i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ (fun h => hij (e.symm.injective h)),
      Matrix.diagonal_apply_ne _ hij]

theorem diagonal_entropy_reindex (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (μ : Measure (X (d+1))) (ell : Fin (d+1) → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) :
    measureEntropy (μ.map (quotientReindex e))
      (fun x => rightAction x (diagonalOneParameter
        (fun i => ell (e.symm i)) (permutedWeight_sum e ell hell) t)) =
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell t)) := by
  exact measureEntropy_map_measurableEquiv μ (quotientReindexHomeomorph e).toMeasurableEquiv
    _ _ (continuous_rightAction _).measurable (continuous_rightAction _).measurable
    (fun x => by
      change quotientReindex e (rightAction x _) = rightAction (quotientReindex e x) _
      rw [quotientReindex_rightAction, reindex_diagonalOneParameter])

end DukePrimeDegree

end

end OAI
